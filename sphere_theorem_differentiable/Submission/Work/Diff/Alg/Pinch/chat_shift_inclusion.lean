import Mathlib
import Submission.Work.Diff.Alg.Pinch.ChatShiftDefs
import Submission.Work.Diff.Alg.Pinch.ChatShift.ric0_form_bound
import Submission.Work.Diff.Alg.Pinch.ChatShift.knProd_ric0_norm_bound
import Submission.Work.Diff.Alg.Pinch.ChatShift.linv_ell_add_smul_Iso
import Submission.Work.Diff.Alg.Pinch.ChatShift.chat_shift_room_b1
import Submission.Work.Diff.Alg.Pinch.ChatShift.chat_shift_room_b2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The shift inclusion `R + c • Iso ∈ Ĉ(s) → R + 2c • Iso ∈ Ĉ(s+ε)`

Let `Ĉ(s) = Chat n s` be the Brendle–Schoen pinching family of `O(n)`-invariant cones of
algebraic curvature tensors (Brendle–Schoen §3).  The main theorem of this file is

`chat_shift_inclusion : ∃ ε > 0, ∃ N > 0, ∀ R, R + c • Iso n ∈ Ĉ(s) → scalAlg R ≤ N*c →
R + (2*c) • Iso n ∈ Ĉ(s + ε)`.

It says that moving a point of `Ĉ(s)` a `c • Iso n`-step further in the round-sphere direction,
where `c` dominates the scalar curvature of the initial tensor, lands in the *smaller* cone
`Ĉ(s+ε)`.

## Mathematical content

Write `X = R + c • Iso n ∈ Ĉ(s)`, `σ = scalAlg X ≥ 0`, `X̂ = σ⁻¹ • X` (so `scalAlg X̂ = 1`) and
`α = u/(1+u)` with `u = (c/σ)·n(n-1)` (for `σ > 0`).  Then

`R + 2c • Iso n = (σ + c·n(n-1)) • Y`,  `Y = (1-α) • X̂ + (α/(n(n-1))) • Iso n`,

and the hypothesis `scalAlg R ≤ 2n(n-1)·c` forces `1/4 ≤ α ≤ 1` (`hα14`).  Since `Ĉ(s+ε)` is a
cone (`ccone_smul_mem`) it suffices to prove `Y ∈ Ĉ(s+ε)`.

In the parametrisation `Ĉ(s) = ℓ_{a,b}(Dpic P)` (the two branches `s ≤ 1/2`, `s ≥ 1/2` of `Chat`,
`Chat_eq_Ccone`, `chat_eq_Ccone_half`), write `X̂ = ℓ_{a,b} S` with `S ∈ Dpic P`; then
`scalAlg S = κ = 1/(1+2(n-1)a)` (`hS1scal`), and with `S2 = (1-α) • S ∈ Dpic P` one has
`Y = ℓ_{a,b} S2 + t • Iso n` with `t = α/(n(n-1))`.  The residual content is the passage from
`Dpic P` at the parameters `(a,b)` to `Dpic P'` at the shifted parameters:
`linv a' b' Y = S2 + γ₁ • (Ric₀ S2 ∧ id) + γ₂ • Iso n` (`linv_ell_add_smul_Iso`), with
`γ₁ = chSg1 n b b'` and `γ₂ = chSg2 n a a' t σ'` (`σ' = scalAlg S2`).  For small `ε` one has
`γ₁ = O(ε)`, `γ₂` bounded below, `a' = a + O(ε)`, `b' = b + O(ε)`, `P ≤ P'`; the two scalar
inequalities `ChSRoom` — proved in the two branches in `chat_shift_room_b1` /
`chat_shift_room_b2` — absorb the `γ₁`-perturbation into the positive `γ₂ • Iso n`-margin, and
`Dpic_shift_core` concludes `linv a' b' Y ∈ Dpic P'`, whence `Y = ℓ_{a'b'}(linv a' b' Y) ∈ Ĉ(s+ε)`
by `ell_linv`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Small structural facts about `Chat n s` -/

/-- For `s ≥ 1/2` the Brendle–Schoen cone `Ĉ(s)` is `ℓ_{s,1/2}(Dpic p)` with
`p = 1 - 4/(n - 2 + 8s)`.  (The two formulas of `Chat` agree at `s = 1/2`.) -/
theorem chat_eq_Ccone_half (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 1 / 2 ≤ s) :
    Chat n s = Ccone (n := n) s (1 / 2) (1 - 4 / ((n : ℝ) - 2 + 8 * s)) := by
  rcases lt_or_eq_of_le hs with h | h
  · rw [Chat, ite_eq_right (not_le.mpr h)]
  · subst h
    rw [Chat, ite_eq_left le_rfl]
    have hnum : 2 * (1 / 2) + ((n : ℝ) - 2) * (1 / 2) ^ 2 = ((n : ℝ) + 2) / 4 := by ring
    have hden : 2 * (1 + ((n : ℝ) - 2) * (1 / 2) ^ 2) = ((n : ℝ) + 2) / 2 := by ring
    have h1 : (2 * (1 / 2) + ((n : ℝ) - 2) * (1 / 2) ^ 2)
          / (2 * (1 + ((n : ℝ) - 2) * (1 / 2) ^ 2)) = 1 / 2 := by
      rw [hnum, hden]
      have hd : (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      ring
    have hD : 1 + ((n : ℝ) - 2) * (1 / 2) ^ 2 = ((n : ℝ) + 2) / 4 := by ring
    have h2 : 1 - 1 / (1 + ((n : ℝ) - 2) * (1 / 2) ^ 2)
        = 1 - 4 / ((n : ℝ) - 2 + 8 * (1 / 2)) := by
      rw [hD, show (n : ℝ) - 2 + 8 * (1 / 2) = (n : ℝ) + 2 from by ring]
      have hd : (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp
    rw [h1, h2]

/-- `Ccone a b p` is closed under multiplication by a nonnegative scalar. -/
theorem ccone_smul_mem {a b p c : ℝ} (hc : 0 ≤ c) {R : Curv4 n}
    (hR : R ∈ Ccone (n := n) a b p) : c • R ∈ Ccone (n := n) a b p := by
  obtain ⟨S, hS, rfl⟩ := hR
  exact ⟨c • S, ⟨isAlgCurv_smul c hS.1, Cone.inPIC2_smul hS.2.1 hc, RicPinch_smul hc hS.2.2⟩,
    by rw [ell_smul]⟩

/-- `Chat n s` is closed under multiplication by a nonnegative scalar. -/
theorem chat_smul_mem_of_nonneg {s c : ℝ} (hc : 0 ≤ c) {R : Curv4 n} (hR : R ∈ Chat n s) :
    c • R ∈ Chat n s := by
  rw [Chat] at hR ⊢
  split_ifs at hR ⊢ with h
  · exact ccone_smul_mem hc hR
  · exact ccone_smul_mem hc hR

/-- `1 + 2(n-1)a > 0` for `n ≥ 2` and `a ≥ 0`. -/
theorem one_add_two_mul_pos {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : 0 ≤ a) :
    0 < 1 + 2 * ((n : ℝ) - 1) * a := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  nlinarith

/-- `chatP n ·` is monotone on `[0, ∞)`. -/
theorem chatP_mono {a b : ℝ} (hn : 2 ≤ n) (ha : 0 ≤ a) (hab : a ≤ b) :
    chatP n a ≤ chatP n b := by
  have h2r : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
  rw [chatP, chatP]
  have hsq : a ^ 2 ≤ b ^ 2 := by nlinarith
  have hmono : 1 + ((n : ℝ) - 2) * a ^ 2 ≤ 1 + ((n : ℝ) - 2) * b ^ 2 := by nlinarith
  have hp1 : 0 < 1 + ((n : ℝ) - 2) * a ^ 2 := by nlinarith [sq_nonneg a]
  have hp2 : 0 < 1 + ((n : ℝ) - 2) * b ^ 2 := by nlinarith [sq_nonneg b]
  have h := one_div_le_one_div_of_le hp1 hmono
  linarith

/-- A positive multiple of the round sphere lies in `Ccone a b p` for `p < 1`. -/
theorem smul_iso_mem_Ccone (n : ℕ) (hn : 2 ≤ n) {a b p c : ℝ} (hp : p < 1) (hc : 0 < c)
    (ha : 0 < 1 + 2 * ((n : ℝ) - 1) * a) : c • Iso n ∈ Ccone (n := n) a b p := by
  have hlam : 0 ≤ c / (1 + 2 * ((n : ℝ) - 1) * a) := div_nonneg hc.le ha.le
  refine ⟨(c / (1 + 2 * ((n : ℝ) - 1) * a)) • Iso n, ?_, ?_⟩
  · refine ⟨isAlgCurv_smul _ (Iso_algCurv n), ?_, RicPinch_smul hlam (ricPinch_iso n hp.le)⟩
    rw [Cone.inPIC2_iff]
    intro x y z w
    rw [Cone.EF_smul]
    exact mul_nonneg hlam ((Cone.inPIC2_iff (Iso n)).mp (Cone.inPIC2_iso n) x y z w)
  · rw [ell_smul, ell_iso, smul_smul]
    congr 1
    rw [show 1 + 2 * a * ((n : ℝ) - 1) = 1 + 2 * ((n : ℝ) - 1) * a from by ring,
      div_mul_cancel₀ c (ne_of_gt ha)]

/-- A positive multiple of the round sphere lies in every `Ĉ(s)`, `s > 0`. -/
theorem smul_iso_mem_chat (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) {c : ℝ} (hc : 0 < c) :
    c • Iso n ∈ Chat n s := by
  by_cases h : s ≤ 1 / 2
  · rw [Chat_eq_Ccone n h]
    exact smul_iso_mem_Ccone n hn (chatP_lt_one (n := n) hn s) hc
      (one_add_two_mul_pos hn (chatA_nonneg hn hs.le))
  · have hs' : 1 / 2 < s := not_le.mp h
    rw [chat_eq_Ccone_half n hn (le_of_lt hs')]
    refine smul_iso_mem_Ccone n hn ?_ hc (one_add_two_mul_pos hn (by linarith))
    have hden : (0 : ℝ) < (n : ℝ) - 2 + 8 * s := by linarith
    have h0 : 0 < 4 / ((n : ℝ) - 2 + 8 * s) := by positivity
    linarith

/-! ## The membership transfer in the `Dpic` picture -/

/-- `ell a b 0 = 0`. -/
theorem ell_zero' (n : ℕ) (a b : ℝ) : ell a b (0 : Curv4 n) = 0 := by
  rw [ell, ric0_zero, knProd_zero_left, smul_zero, add_zero, scalAlg_zero, mul_zero, zero_smul,
    add_zero]

/-- `chSg2` is increasing in the `Iso`-coefficient `t`. -/
theorem chSg2_mono {n : ℕ} {a a' t t' σ : ℝ} (htt : t ≤ t')
    (hD : 0 < 1 + 2 * ((n : ℝ) - 1) * a') : chSg2 n a a' t σ ≤ chSg2 n a a' t' σ := by
  rw [chSg2, chSg2, le_div_iff₀ hD,
    div_mul_cancel₀ (t + 2 * σ * (a - a') / (n : ℝ)) (ne_of_gt hD)]
  linarith

/-- `ChSRoom` is monotone in the `Iso`-coefficient `t`. -/
theorem ChSRoom_mono_le {n : ℕ} {C_EF C_T C_ric a a' b b' P P' t t' σ : ℝ} (htt : t ≤ t')
    (hD : 0 < 1 + 2 * ((n : ℝ) - 1) * a') (hn2 : 2 ≤ n) (hP' : P' ≤ 1)
    (h : ChSRoom n C_EF C_T C_ric a a' b b' P P' t σ) :
    ChSRoom n C_EF C_T C_ric a a' b b' P P' t' σ := by
  have hmono : chSg2 n a a' t σ ≤ chSg2 n a a' t' σ := chSg2_mono htt hD
  have hcoef : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    linarith
  have h1P : (0 : ℝ) ≤ 1 - P' := by linarith
  have hstep1 : chSg2 n a a' t σ * ((n : ℝ) - 1) ≤ chSg2 n a a' t' σ * ((n : ℝ) - 1) :=
    mul_le_mul_of_nonneg_right hmono hcoef
  have hstep2 : chSg2 n a a' t σ * ((n : ℝ) - 1) * (1 - P')
      ≤ chSg2 n a a' t' σ * ((n : ℝ) - 1) * (1 - P') :=
    mul_le_mul_of_nonneg_right hstep1 h1P
  exact ⟨h.1.trans hmono, by linarith [hstep2, h.2]⟩

/-- **Core step.**  If the two "room" inequalities `ChSRoom` hold, then the perturbation
`S ↦ S + γ₁ • (Ric₀ S ∧ id) + γ₂ • Iso n` stays inside `Dpic P'` whenever `S ∈ Dpic P`.

The two `Iso`-directions are harmless (`InPIC2` and `RicPinch` are closed under adding
nonnegative multiples of `Iso n`), the `Ric₀ ∧ id`-direction is absorbed by the rooms:
`C_EF` bounds the isotropic curvature form of an algebraic tensor by `‖D‖ · EF (Iso n)`,
`C_T` bounds `‖Ric₀ S ∧ id‖` and `C_ric` bounds `|⟨Ric₀ S v, v⟩|`, both by `C · scalAlg S`. -/
theorem Dpic_shift_core (n : ℕ) (hn : 2 ≤ n) {C_EF C_T C_ric : ℝ}
    (hC_EF : 0 ≤ C_EF) (hC_T : 0 ≤ C_T) (hC_ric : 0 ≤ C_ric)
    (hEF : ∀ D : Curv4 n, IsAlgCurv D → ∀ x y z w : Fin n → ℝ,
      |Cone.EF D x y z w| ≤ C_EF * ‖D‖ * Cone.EF (Iso n) x y z w)
    (hTb : ∀ S : Curv4 n, IsAlgCurv S → InPIC2 S →
      ‖knProd (ric0 S) (id2 n)‖ ≤ C_T * scalAlg S)
    (hricb : ∀ S : Curv4 n, IsAlgCurv S → InPIC2 S → ∀ v : Fin n → ℝ,
      |∑ i, ∑ j, ric0 S i j * v i * v j| ≤ C_ric * scalAlg S * (∑ i, v i * v i))
    {a a' b b' P P' t σ : ℝ} (hP : P ≤ P') (hP' : P' < 1)
    {S : Curv4 n} (hS : IsAlgCurv S) (hPIC : InPIC2 S) (hRic : RicPinch P S)
    (hσ : scalAlg S = σ)
    (hroom : ChSRoom n C_EF C_T C_ric a a' b b' P P' t σ) :
    S + chSg1 n b b' • knProd (ric0 S) (id2 n) + chSg2 n a a' t σ • Iso n ∈ Dpic (n := n) P' := by
  have hσ0 : 0 ≤ σ := by rw [← hσ]; exact (inPIC2_metric_basic n).2.2 S hPIC
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hTalg : IsAlgCurv (knProd (ric0 S) (id2 n)) :=
    knProd_isAlgCurv (fun i j => ric0_symm hS i j) (fun i j => id2_symm i j)
  have hTbd : ‖knProd (ric0 S) (id2 n)‖ ≤ C_T * σ := by
    rw [← hσ]; exact hTb S hS hPIC
  have hricbd : ∀ v : Fin n → ℝ,
      |∑ i, ∑ j, ric0 S i j * v i * v j| ≤ C_ric * σ * (∑ i, v i * v i) := by
    intro v; rw [← hσ]; exact hricb S hS hPIC v
  refine ⟨?_, ?_, ?_⟩
  · exact isAlgCurv_add (isAlgCurv_add hS (isAlgCurv_smul _ hTalg))
      (isAlgCurv_smul _ (Iso_algCurv n))
  · rw [Cone.inPIC2_iff]
    intro x y z w
    have hIso : 0 ≤ Cone.EF (Iso n) x y z w :=
      (Cone.inPIC2_iff (Iso n)).mp (Cone.inPIC2_iso n) x y z w
    have hSnn : 0 ≤ Cone.EF S x y z w := (Cone.inPIC2_iff S).mp hPIC x y z w
    have hEFT : |Cone.EF (knProd (ric0 S) (id2 n)) x y z w|
        ≤ C_EF * (C_T * σ) * Cone.EF (Iso n) x y z w := by
      refine (hEF _ hTalg x y z w).trans ?_
      have h1 := mul_le_mul_of_nonneg_left hTbd hC_EF
      have h2 := mul_le_mul_of_nonneg_right h1 hIso
      linarith
    have hg : -( |chSg1 n b b'| * (C_EF * (C_T * σ)) * Cone.EF (Iso n) x y z w)
        ≤ chSg1 n b b' * Cone.EF (knProd (ric0 S) (id2 n)) x y z w := by
      have h1 : -( |chSg1 n b b'| * |Cone.EF (knProd (ric0 S) (id2 n)) x y z w|)
          ≤ chSg1 n b b' * Cone.EF (knProd (ric0 S) (id2 n)) x y z w := by
        have h := neg_abs_le (chSg1 n b b' * Cone.EF (knProd (ric0 S) (id2 n)) x y z w)
        rw [abs_mul] at h
        linarith
      have h2 : |chSg1 n b b'| * |Cone.EF (knProd (ric0 S) (id2 n)) x y z w|
          ≤ |chSg1 n b b'| * (C_EF * (C_T * σ) * Cone.EF (Iso n) x y z w) :=
        mul_le_mul_of_nonneg_left hEFT (abs_nonneg _)
      linarith
    have hmul : |chSg1 n b b'| * C_EF * C_T * σ * Cone.EF (Iso n) x y z w
        ≤ chSg2 n a a' t σ * Cone.EF (Iso n) x y z w :=
      mul_le_mul_of_nonneg_right hroom.1 hIso
    have hsplit : Cone.EF (S + chSg1 n b b' • knProd (ric0 S) (id2 n)
        + chSg2 n a a' t σ • Iso n) x y z w
        = Cone.EF S x y z w + chSg1 n b b' * Cone.EF (knProd (ric0 S) (id2 n)) x y z w
          + chSg2 n a a' t σ * Cone.EF (Iso n) x y z w := by
      simp only [Cone.EF_add, Cone.EF_smul]
    rw [hsplit]
    linarith
  · intro v
    set V : ℝ := ∑ i, v i * v i with hVdef
    have hV0 : 0 ≤ V := by
      rw [hVdef]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
    have hric0v : -(C_ric * σ * V) ≤ ∑ i, ∑ j, ric0 S i j * v i * v j := by
      have h := (abs_le.mp (hricbd v)).1
      rw [← hVdef] at h
      linarith
    have hric0v' : |∑ i, ∑ j, ric0 S i j * v i * v j| ≤ C_ric * σ * V := by
      have h := hricbd v
      rwa [← hVdef] at h
    have hricS : (P * σ / (n : ℝ)) * V ≤ ∑ i, ∑ j, ric S i j * v i * v j := by
      have h := hRic v
      rw [hσ] at h
      simpa [hVdef] using h
    have hricPt : ∀ i j : Fin n,
        ric (S + chSg1 n b b' • knProd (ric0 S) (id2 n) + chSg2 n a a' t σ • Iso n) i j
        = ric S i j + chSg1 n b b' * (((n : ℝ) - 2) * ric0 S i j)
          + chSg2 n a a' t σ * (((n : ℝ) - 1) * id2 n i j) := by
      intro i j
      simp only [ric_add, ric_smul, ric_knProd_ric0_id2, ric_iso] <;> ring
    have hsumA : (∑ i, ∑ j, (ric S i j + chSg1 n b b' * (((n : ℝ) - 2) * ric0 S i j)
          + chSg2 n a a' t σ * (((n : ℝ) - 1) * id2 n i j)) * v i * v j)
        = (∑ i, ∑ j, ric S i j * v i * v j)
          + (chSg1 n b b' * ((n : ℝ) - 2)) * (∑ i, ∑ j, ric0 S i j * v i * v j)
          + (chSg2 n a a' t σ * ((n : ℝ) - 1)) * V := by
      have hB : (∑ i, ∑ j, (chSg1 n b b' * (((n : ℝ) - 2) * ric0 S i j)) * v i * v j)
          = (chSg1 n b b' * ((n : ℝ) - 2)) * (∑ i, ∑ j, ric0 S i j * v i * v j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        ring
      have hC : (∑ i, ∑ j, (chSg2 n a a' t σ * (((n : ℝ) - 1) * id2 n i j)) * v i * v j)
          = (chSg2 n a a' t σ * ((n : ℝ) - 1)) * V := by
        have hpt : ∀ i j : Fin n,
            (chSg2 n a a' t σ * (((n : ℝ) - 1) * id2 n i j)) * v i * v j
              = (chSg2 n a a' t σ * ((n : ℝ) - 1)) * (id2 n i j * v i * v j) := by
          intro i j; ring
        rw [hVdef]
        calc (∑ i, ∑ j, (chSg2 n a a' t σ * (((n : ℝ) - 1) * id2 n i j)) * v i * v j)
            = ∑ i, ∑ j, (chSg2 n a a' t σ * ((n : ℝ) - 1)) * (id2 n i j * v i * v j) := by
              apply Finset.sum_congr rfl; intro i _
              apply Finset.sum_congr rfl; intro j _
              rw [hpt i j]
          _ = (chSg2 n a a' t σ * ((n : ℝ) - 1)) * (∑ i, ∑ j, id2 n i j * v i * v j) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro i _
              rw [Finset.mul_sum]
          _ = (chSg2 n a a' t σ * ((n : ℝ) - 1)) * (∑ i, v i * v i) := by
              congr 1
              apply Finset.sum_congr rfl; intro i _
              have h1 : (∑ j, id2 n i j * v i * v j) = v i * (∑ j, id2 n i j * v j) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl; intro j _; ring
              rw [h1, ellinv_sum_id2_mul]
      have hsplit : (∑ i, ∑ j, (ric S i j + chSg1 n b b' * (((n : ℝ) - 2) * ric0 S i j)
            + chSg2 n a a' t σ * (((n : ℝ) - 1) * id2 n i j)) * v i * v j)
          = (∑ i, ∑ j, ric S i j * v i * v j)
            + (∑ i, ∑ j, (chSg1 n b b' * (((n : ℝ) - 2) * ric0 S i j)) * v i * v j)
            + (∑ i, ∑ j, (chSg2 n a a' t σ * (((n : ℝ) - 1) * id2 n i j)) * v i * v j) := by
        simp only [add_mul, Finset.sum_add_distrib]
      rw [hsplit, hB, hC]
    have hsum : (∑ i, ∑ j,
          ric (S + chSg1 n b b' • knProd (ric0 S) (id2 n) + chSg2 n a a' t σ • Iso n) i j
            * v i * v j)
        = (∑ i, ∑ j, ric S i j * v i * v j)
          + (chSg1 n b b' * ((n : ℝ) - 2)) * (∑ i, ∑ j, ric0 S i j * v i * v j)
          + (chSg2 n a a' t σ * ((n : ℝ) - 1)) * V := by
      rw [show (∑ i, ∑ j,
            ric (S + chSg1 n b b' • knProd (ric0 S) (id2 n) + chSg2 n a a' t σ • Iso n) i j
              * v i * v j)
          = ∑ i, ∑ j, (ric S i j + chSg1 n b b' * (((n : ℝ) - 2) * ric0 S i j)
              + chSg2 n a a' t σ * (((n : ℝ) - 1) * id2 n i j)) * v i * v j from by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [hricPt i j]]
      exact hsumA
    have hscal' : scalAlg (S + chSg1 n b b' • knProd (ric0 S) (id2 n)
          + chSg2 n a a' t σ • Iso n)
        = σ + chSg2 n a a' t σ * ((n : ℝ) * ((n : ℝ) - 1)) := by
      rw [scalAlg_add, scalAlg_add, scalAlg_smul, scalAlg_smul, scalAlg_knProd_ric0, hσ, scalAlg_iso]
      ring
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hroom' : (chSg2 n a a' t σ * ((n : ℝ) - 1)) * V - (P' * chSg2 n a a' t σ * ((n : ℝ) - 1)) * V
        ≥ (|chSg1 n b b'| * ((n : ℝ) - 2) * C_ric * σ) * V + (σ * (P' - P) / (n : ℝ)) * V := by
      have h := mul_le_mul_of_nonneg_right hroom.2 hV0
      have he : (chSg2 n a a' t σ * ((n : ℝ) - 1) * (1 - P')) * V
          = (chSg2 n a a' t σ * ((n : ℝ) - 1)) * V
            - (P' * chSg2 n a a' t σ * ((n : ℝ) - 1)) * V := by ring
      have he2 : (|chSg1 n b b'| * ((n : ℝ) - 2) * C_ric * σ + σ * (P' - P) / (n : ℝ)) * V
          = (|chSg1 n b b'| * ((n : ℝ) - 2) * C_ric * σ) * V
            + (σ * (P' - P) / (n : ℝ)) * V := by
        rw [add_mul, mul_div_assoc]
      rw [he, he2] at h
      linarith
    have hγ₁'' : (chSg1 n b b' * ((n : ℝ) - 2)) * (∑ i, ∑ j, ric0 S i j * v i * v j)
        ≥ -((|chSg1 n b b'| * ((n : ℝ) - 2) * C_ric * σ) * V) := by
      have h1 : -( |chSg1 n b b' * ((n : ℝ) - 2)| * |∑ i, ∑ j, ric0 S i j * v i * v j|)
          ≤ (chSg1 n b b' * ((n : ℝ) - 2)) * (∑ i, ∑ j, ric0 S i j * v i * v j) := by
        have h := neg_abs_le ((chSg1 n b b' * ((n : ℝ) - 2))
          * (∑ i, ∑ j, ric0 S i j * v i * v j))
        rw [abs_mul] at h
        linarith
      have hc1n : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith
      have h2 : |chSg1 n b b' * ((n : ℝ) - 2)| * |∑ i, ∑ j, ric0 S i j * v i * v j|
          ≤ |chSg1 n b b'| * ((n : ℝ) - 2) * (C_ric * σ * V) := by
        have h3 : |chSg1 n b b' * ((n : ℝ) - 2)| = |chSg1 n b b'| * ((n : ℝ) - 2) := by
          rw [abs_mul, abs_of_nonneg hc1n]
        rw [h3]
        exact mul_le_mul_of_nonneg_left hric0v' (by positivity)
      linarith
    have hA : (P' * (σ + chSg2 n a a' t σ * ((n : ℝ) * ((n : ℝ) - 1))) / (n : ℝ)) * V
        = (P * σ / (n : ℝ)) * V + (σ * (P' - P) / (n : ℝ)) * V
          + (P' * chSg2 n a a' t σ * ((n : ℝ) - 1)) * V := by
      have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn0
      field_simp
      ring
    rw [hscal', hsum, hA]
    linarith [hricS, hγ₁'', hroom']

/-! ## The `Ĉ(s)`-step -/

/-- The shift step of the proof, in the `Dpic` picture: if `R + c • Iso n ∈ ℓ_{A,B}(Dpic P)` and
`scalAlg R ≤ 2n(n-1)c`, then `R + 2c • Iso n ∈ ℓ_{A',B'}(Dpic P')`, provided the room conditions
`ChSRoom` hold for the shifted parameters (in the normalised range `1/4 ≤ α ≤ 1`,
`σ ≤ 1/(1+2(n-1)A)`). -/
theorem chat_shift_step (n : ℕ) (hn : 2 ≤ n) {C_EF C_T C_ric : ℝ}
    (hC_EF : 0 ≤ C_EF) (hC_T : 0 ≤ C_T) (hC_ric : 0 ≤ C_ric)
    (hEF : ∀ D : Curv4 n, IsAlgCurv D → ∀ x y z w : Fin n → ℝ,
      |Cone.EF D x y z w| ≤ C_EF * ‖D‖ * Cone.EF (Iso n) x y z w)
    (hTb : ∀ S : Curv4 n, IsAlgCurv S → InPIC2 S →
      ‖knProd (ric0 S) (id2 n)‖ ≤ C_T * scalAlg S)
    (hricb : ∀ S : Curv4 n, IsAlgCurv S → InPIC2 S → ∀ v : Fin n → ℝ,
      |∑ i, ∑ j, ric0 S i j * v i * v j| ≤ C_ric * scalAlg S * (∑ i, v i * v i))
    {A B P A' B' P' : ℝ} (hA : 0 < 1 + 2 * ((n : ℝ) - 1) * A)
    (hA' : 0 < 1 + 2 * ((n : ℝ) - 1) * A') (hB' : 0 < 1 + ((n : ℝ) - 2) * B')
    (hP : P ≤ P') (hP' : P' < 1)
    (hroom : ∀ α σ : ℝ, 1 / 4 ≤ α → α ≤ 1 → 0 < σ →
      σ ≤ 1 / (1 + 2 * ((n : ℝ) - 1) * A) →
      ChSRoom n C_EF C_T C_ric A A' B B' P P' (α / ((n : ℝ) * ((n : ℝ) - 1))) σ)
    {c : ℝ} (hc : 0 < c) {R : Curv4 n}
    (hX : R + c • Iso n ∈ Ccone (n := n) A B P)
    (hscal : scalAlg R ≤ 2 * ((n : ℝ) * ((n : ℝ) - 1)) * c) :
    R + (2 * c) • Iso n ∈ Ccone (n := n) A' B' P' := by
  set κ : ℝ := 1 / (1 + 2 * ((n : ℝ) - 1) * A) with hκdef
  have hκpos : 0 < κ := by rw [hκdef]; positivity
  have hn2ℝ : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnℝ : (0 : ℝ) < (n : ℝ) := by linarith
  have hnn : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := mul_pos hnℝ (by linarith)
  obtain ⟨S0, hS0mem, hS0eq⟩ := hX
  have hσS0 : 0 ≤ scalAlg S0 := (inPIC2_metric_basic n).2.2 S0 hS0mem.2.1
  have hσX : scalAlg (R + c • Iso n) = (1 + 2 * ((n : ℝ) - 1) * A) * scalAlg S0 := by
    rw [← hS0eq, scalAlg_ell]
  have hσX0 : 0 ≤ scalAlg (R + c • Iso n) := by
    rw [hσX]; exact mul_nonneg hA.le hσS0
  by_cases hz : scalAlg (R + c • Iso n) = 0
  · have hS00 : scalAlg S0 = 0 := by
      have h := hσX
      rw [hz] at h
      rcases mul_eq_zero.mp h.symm with h' | h'
      · exact absurd h' (ne_of_gt hA)
      · exact h'
    have hX0 : R + c • Iso n = 0 := by
      rw [← hS0eq, (inPIC2_comp_bound n).2 S0 hS0mem.2.1 hS00, ell_zero' n A B]
    have hReq : R = -(c • Iso n) := by
      rw [eq_neg_iff_add_eq_zero]; exact hX0
    have hgoal : R + (2 * c) • Iso n = c • Iso n := by rw [hReq]; module
    rw [hgoal]
    exact smul_iso_mem_Ccone n hn hP' hc hA'
  · have hσpos : 0 < scalAlg (R + c • Iso n) := lt_of_le_of_ne hσX0 (Ne.symm hz)
    set σ : ℝ := scalAlg (R + c • Iso n) with hσdef
    have hσpos' : 0 < σ := hσpos
    set S1 : Curv4 n := σ⁻¹ • S0 with hS1def
    have hσinv0 : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσX0
    have hS1mem : S1 ∈ Dpic (n := n) P :=
      ⟨isAlgCurv_smul _ hS0mem.1, Cone.inPIC2_smul hS0mem.2.1 hσinv0,
        RicPinch_smul hσinv0 hS0mem.2.2⟩
    have hXhat : σ⁻¹ • (R + c • Iso n) = ell A B S1 := by
      rw [hS1def, ← hS0eq, ← ell_smul]
    have hS1scal : scalAlg S1 = κ := by
      have h1 : (1 + 2 * ((n : ℝ) - 1) * A) * scalAlg S1 = 1 := by
        have h2 : σ⁻¹ * σ = 1 := inv_mul_cancel₀ (ne_of_gt hσpos')
        have h3 : scalAlg (σ⁻¹ • (R + c • Iso n)) = σ⁻¹ * σ := by
          rw [scalAlg_smul, ← hσdef]
        rw [hXhat, scalAlg_ell] at h3
        rw [h3, h2]
      rw [hκdef, eq_div_iff (ne_of_gt hA)]
      linarith
    have hS1pos : 0 < scalAlg S1 := by rw [hS1scal]; exact hκpos
    have hS1le : scalAlg S1 ≤ 1 / (1 + 2 * ((n : ℝ) - 1) * A) := by
      rw [hS1scal, hκdef]
    set τ : ℝ := c / σ with hτdef
    have hτpos : 0 < τ := div_pos hc hσpos'
    have hτge : (1 / 4) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ τ := by
      have hσle : σ ≤ 3 * ((n : ℝ) * ((n : ℝ) - 1)) * c := by
        have h : σ = scalAlg R + c * ((n : ℝ) * ((n : ℝ) - 1)) := by
          rw [hσdef, scalAlg_add, scalAlg_smul, scalAlg_iso]
        rw [h]; nlinarith [hscal, hc]
      rw [hτdef, div_div, div_le_iff₀ (by linarith : (0 : ℝ) < 4 * ((n : ℝ) * ((n : ℝ) - 1))),
        div_mul_eq_mul_div, le_div_iff₀ hσpos']
      nlinarith [hσle, hc]
    have hroom0 := hroom (1 / 4) (scalAlg S1) (by norm_num) (by norm_num) hS1pos hS1le
    have hroom' : ChSRoom n C_EF C_T C_ric A A' B B' P P' τ (scalAlg S1) :=
      ChSRoom_mono_le hτge hA' hn hP'.le hroom0
    have hcore := Dpic_shift_core n hn hC_EF hC_T hC_ric hEF hTb hricb hP hP'
      hS1mem.1 hS1mem.2.1 hS1mem.2.2 rfl hroom'
    set Y : Curv4 n := σ⁻¹ • (R + c • Iso n) + τ • Iso n with hYdef
    have hYell : Y = ell A B S1 + τ • Iso n := by rw [hYdef, hXhat]
    have hlinv : linv A' B' Y = S1 + chSg1 n B B' • knProd (ric0 S1) (id2 n)
        + chSg2 n A A' τ (scalAlg S1) • Iso n := by
      rw [hYell]
      exact ChatShift.linv_ell_add_smul_Iso n hS1mem.1 (ne_of_gt hA') (ne_of_gt hB')
    have hDmem : linv A' B' Y ∈ Dpic (n := n) P' := by
      rw [hlinv]; exact hcore
    have hYalg : IsAlgCurv Y := by
      rw [hYell]
      exact isAlgCurv_add (ell_isAlgCurv n A B hS1mem.1) (isAlgCurv_smul _ (Iso_algCurv n))
    have hYmem : Y ∈ Ccone (n := n) A' B' P' :=
      ⟨linv A' B' Y, hDmem, ell_linv n (ne_of_gt hA') (ne_of_gt hB') hYalg⟩
    have hZ : R + (2 * c) • Iso n = σ • Y := by
      rw [hYdef, smul_add]
      simp only [smul_smul]
      have e1 : σ * σ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hσpos')
      have e2 : σ * τ = c := by
        rw [hτdef, mul_comm σ (c / σ)]
        exact div_mul_cancel₀ c (ne_of_gt hσpos')
      rw [e1, e2, one_smul]
      module
    rw [hZ]
    exact ccone_smul_mem hσX0 hYmem

/-! ## The target theorem -/

theorem chat_shift_inclusion (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) (c : ℝ) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℝ, 0 < N ∧ ∀ R : Submission.Diff.Alg.Curv4 n,
      R + c • Submission.Diff.Alg.Iso n ∈ Work.Diff.Alg.Pinch.Chat n s →
      Submission.Diff.Alg.scalAlg R ≤ N * c →
      R + (2 * c) • Submission.Diff.Alg.Iso n ∈ Work.Diff.Alg.Pinch.Chat n (s + ε) := by
  have hNpos : (0 : ℝ) < 2 * ((n : ℝ) * ((n : ℝ) - 1)) := by
    have h2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  obtain ⟨C_EF, hC_EF0, hC_EF⟩ := EF_algCurv_bound n
  obtain ⟨C_T, hC_T0, hC_T⟩ := ChatShift.knProd_ric0_norm_bound n
  obtain ⟨C_ric, hC_ric0, hC_ric⟩ := ChatShift.ric0_form_bound n
  rcases lt_or_ge s (1 / 2) with hs2 | hs2
  · obtain ⟨ε₀, hε₀pos, hε₀le, hroom⟩ :=
      ChatShift.chat_shift_room_b1 n hn C_EF C_T C_ric hC_EF0.le hC_T0 hC_ric0 s hs hs2
    refine ⟨ε₀, hε₀pos, 2 * ((n : ℝ) * ((n : ℝ) - 1)), hNpos, ?_⟩
    intro R hX hscalR
    rw [Chat_eq_Ccone n (le_of_lt hs2)] at hX
    rw [Chat_eq_Ccone n (by linarith : s + ε₀ ≤ 1 / 2)]
    refine chat_shift_step n hn hC_EF0.le hC_T0 hC_ric0 hC_EF hC_T hC_ric
      (one_add_two_mul_pos hn (chatA_nonneg hn hs.le)) ?_ ?_ ?_ ?_ ?_ hc hX ?_
    · exact one_add_two_mul_pos hn (chatA_nonneg hn (by linarith))
    · have h2r : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
      nlinarith
    · exact chatP_mono hn hs.le (by linarith)
    · exact chatP_lt_one (n := n) hn (s + ε₀)
    · intro α σ hα1 hα2 hσ0 hσle
      exact hroom ε₀ hε₀pos le_rfl α σ hα1 hα2 hσ0 hσle
    · linarith [hscalR]
  · obtain ⟨ε₀, hε₀pos, hε₀le, hroom⟩ :=
      ChatShift.chat_shift_room_b2 n hn C_EF C_T C_ric hC_EF0.le hC_T0 hC_ric0 s hs2
    refine ⟨ε₀, hε₀pos, 2 * ((n : ℝ) * ((n : ℝ) - 1)), hNpos, ?_⟩
    intro R hX hscalR
    rw [chat_eq_Ccone_half n hn hs2] at hX
    rw [chat_eq_Ccone_half n hn (by linarith : 1 / 2 ≤ s + ε₀)]
    refine chat_shift_step n hn hC_EF0.le hC_T0 hC_ric0 hC_EF hC_T hC_ric
      (one_add_two_mul_pos hn (by linarith)) (one_add_two_mul_pos hn (by linarith))
      (by have : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn; nlinarith) ?_ ?_ ?_ hc hX ?_
    · have hden : (0 : ℝ) < (n : ℝ) - 2 + 8 * s := by linarith
      have hden' : (0 : ℝ) < (n : ℝ) - 2 + 8 * (s + ε₀) := by linarith
      have h1 : 4 / ((n : ℝ) - 2 + 8 * s) ≥ 4 / ((n : ℝ) - 2 + 8 * (s + ε₀)) := by
        apply div_le_div_of_nonneg_left (by norm_num) hden
        linarith
      linarith
    · have hden' : (0 : ℝ) < (n : ℝ) - 2 + 8 * (s + ε₀) := by linarith
      have h0 : 0 < 4 / ((n : ℝ) - 2 + 8 * (s + ε₀)) := by positivity
      linarith [h0]
    · intro α σ hα1 hα2 hσ0 hσle
      exact hroom ε₀ hε₀pos le_rfl α σ hα1 hα2 hσ0 hσle
    · linarith [hscalR]

end Work.Diff.Alg.Pinch
