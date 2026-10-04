import Mathlib
import Submission.Work.Diff.Alg.Pinch.Chat
import Submission.Work.Diff.Alg.Pinch.ChatDefs
import Submission.Work.Diff.Alg.Pinch.Chat_margin
import Submission.Work.Diff.Alg.Pinch.Q_lipschitz_local
import Submission.Work.Diff.Alg.Pinch.inPIC2_comp_bound
import Submission.Work.Diff.Alg.Pinch.Q_isAlgCurv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Base facts for the shifted-cone room lemma `Chat_shift_room`

Vocabulary shared by `Work.Diff.Alg.Pinch.Chat_shift_room` and its helper lemmas:

* the Brendle–Schoen family `Chat n s = Ĉ(s)` as a *single* cone
  `Ccone (chatAA n s) (chatBB s) (chatPP n s)` with parameters continuous in `s > 0`;
* elementary facts: `Chat n s` consists of algebraic curvature tensors, it is a cone containing
  `Iso n`, and `scalAlg` is nonnegative there with equality only at `0`;
* quantitative bounds: componentwise bounds for `ell a b` and `linv a b` (for `a, b ≥ 0`) and the
  resulting uniform bound `‖X‖ ≤ C * scalAlg X` on `Chat n s`, `s ∈ [s₀, T]`;
* the clamped inverse `chatLinv`, a globally continuous function of `(s, Y)` agreeing with
  `linv (chatAA n s) (chatBB s)` for `s ≥ 0`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## 1. The family as a single continuous family of cones -/

/-- The `a`-parameter of `Ĉ(s)` (`chatA n s` for `0 < s ≤ 1/2`, `s` for `s ≥ 1/2`). -/
noncomputable def chatAA (n : ℕ) (s : ℝ) : ℝ := chatA n (min s (1 / 2)) + max (s - 1 / 2) 0

/-- The `b`-parameter of `Ĉ(s)` (`s` for `0 < s ≤ 1/2`, `1/2` for `s ≥ 1/2`). -/
noncomputable def chatBB (s : ℝ) : ℝ := min s (1 / 2)

/-- The `p`-parameter of `Ĉ(s)` (`chatP n s` for `0 < s ≤ 1/2`,
`1 - 4/((n-2) + 8s)` for `s ≥ 1/2`). -/
noncomputable def chatPP (n : ℕ) (s : ℝ) : ℝ :=
  (1 - 4 / ((n : ℝ) - 2 + 8 * max s (1 / 2))) + (chatP n (min s (1 / 2)) - chatP n (1 / 2))

lemma chatA_half (n : ℕ) : chatA n (1 / 2) = 1 / 2 := by
  have hb : (2 : ℝ) * (1 + ((n : ℝ) - 2) * (1 / 2) ^ 2) ≠ 0 := by
    have h2 := Nat.cast_nonneg (α := ℝ) n
    exact ne_of_gt (by nlinarith)
  rw [chatA, div_eq_iff hb]
  ring

lemma chatP_half (n : ℕ) : chatP n (1 / 2) = 1 - 4 / ((n : ℝ) - 2 + 8 * (1 / 2)) := by
  have hb1 : 1 + ((n : ℝ) - 2) * (1 / 2) ^ 2 ≠ 0 := by
    have h2 := Nat.cast_nonneg (α := ℝ) n
    exact ne_of_gt (by nlinarith)
  have hb2 : (n : ℝ) - 2 + 8 * (1 / 2) ≠ 0 := by
    have h2 := Nat.cast_nonneg (α := ℝ) n
    exact ne_of_gt (by nlinarith)
  rw [chatP]
  congr 1
  rw [div_eq_div_iff hb1 hb2]
  ring

lemma chatAA_eq (n : ℕ) (s : ℝ) : chatAA n s = if s ≤ 1 / 2 then chatA n s else s := by
  by_cases h : s ≤ 1 / 2
  · rw [if_pos h, chatAA, min_eq_left h, max_eq_right (by linarith)]; ring
  · rw [if_neg h, chatAA, min_eq_right (le_of_lt (not_le.mp h)), max_eq_left (by linarith),
      chatA_half n]; ring

lemma chatBB_eq (s : ℝ) : chatBB s = if s ≤ 1 / 2 then s else 1 / 2 := by
  by_cases h : s ≤ 1 / 2
  · rw [if_pos h, chatBB, min_eq_left h]
  · rw [if_neg h, chatBB, min_eq_right (le_of_lt (not_le.mp h))]

lemma chatPP_eq (n : ℕ) (s : ℝ) :
    chatPP n s = if s ≤ 1 / 2 then chatP n s else 1 - 4 / ((n : ℝ) - 2 + 8 * s) := by
  by_cases h : s ≤ 1 / 2
  · rw [if_pos h, chatPP, min_eq_left h, max_eq_right h, chatP_half n]; ring
  · rw [if_neg h, chatPP, min_eq_right (le_of_lt (not_le.mp h)),
      max_eq_left (le_of_lt (not_le.mp h)), chatP_half n]; ring

/-- The whole family is the single cone `Ccone (chatAA n s) (chatBB s) (chatPP n s)`. -/
lemma chat_eq_Ccone_param (n : ℕ) {s : ℝ} :
    Chat n s = Ccone (n := n) (chatAA n s) (chatBB s) (chatPP n s) := by
  rw [chatAA_eq, chatBB_eq, chatPP_eq, Chat]
  split_ifs <;> rfl

lemma continuous_chatA (n : ℕ) (hn : 2 ≤ n) : Continuous (chatA n) := by
  have h : chatA n = fun s : ℝ =>
      (2 * s + ((n : ℝ) - 2) * s ^ 2) / (2 * (1 + ((n : ℝ) - 2) * s ^ 2)) := by
    funext s; rw [chatA]
  rw [h]
  refine Continuous.div (by fun_prop) (by fun_prop) (fun s => ?_)
  have := chatA_denom_pos hn s
  positivity

lemma continuous_chatP (n : ℕ) (hn : 2 ≤ n) : Continuous (chatP n) := by
  have h : chatP n = fun s : ℝ => 1 - 1 / (1 + ((n : ℝ) - 2) * s ^ 2) := by
    funext s; rw [chatP]
  rw [h]
  refine Continuous.sub continuous_const
    (Continuous.div continuous_const (by fun_prop) (fun s => ?_))
  have := chatA_denom_pos hn s
  linarith

lemma continuous_chatAA (n : ℕ) (hn : 2 ≤ n) : Continuous (chatAA n) := by
  have h : chatAA n = fun s : ℝ => chatA n (min s (1 / 2)) + max (s - 1 / 2) 0 := rfl
  rw [h]
  exact ((continuous_chatA n hn).comp (continuous_id.min continuous_const)).add
    ((continuous_id.sub continuous_const).max continuous_const)

lemma continuous_chatBB : Continuous (fun s : ℝ => chatBB s) := by
  have h : chatBB = fun s : ℝ => min s (1 / 2) := rfl
  rw [h]
  exact continuous_id.min continuous_const

lemma continuous_chatPP (n : ℕ) (hn : 2 ≤ n) : Continuous (chatPP n) := by
  have h : chatPP n = fun s : ℝ => (1 - 4 / ((n : ℝ) - 2 + 8 * max s (1 / 2)))
      + (chatP n (min s (1 / 2)) - chatP n (1 / 2)) := rfl
  rw [h]
  refine (continuous_const.sub ?_).add (((continuous_chatP n hn).comp
    (continuous_id.min continuous_const)).sub continuous_const)
  refine Continuous.div continuous_const (by fun_prop) (fun s => ?_)
  have h2 : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
  have h3 : (1 / 2 : ℝ) ≤ max s (1 / 2) := le_max_right _ _
  nlinarith

/-! ### Bounds on the parameters -/

lemma chatA_le_half (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : s ≤ 1 / 2) : chatA n s ≤ 1 / 2 := by
  have hd : 0 < 2 * (1 + ((n : ℝ) - 2) * s ^ 2) := by
    have := chatA_denom_pos hn s; linarith
  rw [chatA, div_le_iff₀ hd]
  nlinarith

lemma chatAA_nonneg (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ chatAA n s := by
  rw [chatAA]
  have h1 : 0 ≤ chatA n (min s (1 / 2)) := chatA_nonneg hn (le_min hs (by norm_num))
  have h2 : 0 ≤ max (s - 1 / 2) 0 := le_max_right _ _
  linarith

lemma chatAA_le (n : ℕ) (hn : 2 ≤ n) {s T : ℝ} (hs : s ≤ T) :
    chatAA n s ≤ max (1 / 2 : ℝ) T := by
  by_cases h : s ≤ 1 / 2
  · have h1 : min s (1 / 2) = s := min_eq_left h
    have h2 : max (s - 1 / 2) 0 = 0 := max_eq_right (by linarith)
    rw [chatAA, h1, h2, add_zero]
    exact le_trans (chatA_le_half n hn h) (le_max_left _ _)
  · have h1 : min s (1 / 2) = 1 / 2 := min_eq_right (le_of_lt (not_le.mp h))
    have h2 : max (s - 1 / 2) 0 = s - 1 / 2 := max_eq_left (by linarith)
    rw [chatAA, h1, h2, chatA_half]
    have : (1 : ℝ) / 2 + (s - 1 / 2) = s := by ring
    rw [this]
    exact le_trans hs (le_max_right _ _)

lemma chatBB_pos {s : ℝ} (hs : 0 < s) : 0 < chatBB s := lt_min hs (by norm_num)

lemma chatBB_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ chatBB s := le_min hs (by norm_num)

lemma chatBB_le_half (s : ℝ) : chatBB s ≤ 1 / 2 := min_le_right _ _

lemma chatPP_lt_one (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) : chatPP n s < 1 := by
  rw [chatPP_eq]
  split_ifs with h
  · exact chatP_lt_one hn s
  · have h2 : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
    have hden : 0 < (n : ℝ) - 2 + 8 * s := by nlinarith
    have : 0 < 4 / ((n : ℝ) - 2 + 8 * s) := div_pos (by norm_num) hden
    linarith

lemma chatAA_denom (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 ≤ s) :
    1 + 2 * ((n : ℝ) - 1) * chatAA n s ≠ 0 := by
  have h1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h2 := chatAA_nonneg n hn hs
  have : (0 : ℝ) < 1 + 2 * ((n : ℝ) - 1) * chatAA n s := by nlinarith
  exact ne_of_gt this

lemma chatBB_denom (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 ≤ s) :
    1 + ((n : ℝ) - 2) * chatBB s ≠ 0 := by
  have h2 : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
  have h3 := chatBB_nonneg hs
  have : (0 : ℝ) < 1 + ((n : ℝ) - 2) * chatBB s := by nlinarith
  exact ne_of_gt this


/-! ## 1b. Structural facts about the cones (self-contained)

These repeat the facts previously imported from `chat_odeInvariant.lean`, with names prefixed by
`csb_` (so that this file can be built without the modules whose duplicate declarations
(`Ccone_transversal_a_aux` vs `Cone_transversal_b`/`linv_Q_ell`) currently clash). -/

theorem csb_isClosed_isAlgCurv (n : ℕ) : IsClosed {R : Curv4 n | IsAlgCurv R} := by
  have h : {R : Curv4 n | IsAlgCurv R} =
      ({R : Curv4 n | ∀ i j k l, R j i k l = - R i j k l} ∩
        {R : Curv4 n | ∀ i j k l, R k l i j = R i j k l}) ∩
        {R : Curv4 n | ∀ i j k l, R i j k l + R j k i l + R k i j l = 0} := by
    ext R
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, IsAlgCurv]
    tauto
  rw [h]
  refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
  · rw [show {R : Curv4 n | ∀ i j k l, R j i k l = - R i j k l}
        = ⋂ i, ⋂ j, ⋂ k, ⋂ l, {R : Curv4 n | R j i k l = - R i j k l} from by
      ext R; simp only [Set.mem_setOf_eq, Set.mem_iInter]]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun k =>
      isClosed_iInter fun l => isClosed_eq (by fun_prop) (by fun_prop)
  · rw [show {R : Curv4 n | ∀ i j k l, R k l i j = R i j k l}
        = ⋂ i, ⋂ j, ⋂ k, ⋂ l, {R : Curv4 n | R k l i j = R i j k l} from by
      ext R; simp only [Set.mem_setOf_eq, Set.mem_iInter]]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun k =>
      isClosed_iInter fun l => isClosed_eq (by fun_prop) (by fun_prop)
  · rw [show {R : Curv4 n | ∀ i j k l, R i j k l + R j k i l + R k i j l = 0}
        = ⋂ i, ⋂ j, ⋂ k, ⋂ l, {R : Curv4 n | R i j k l + R j k i l + R k i j l = 0} from by
      ext R; simp only [Set.mem_setOf_eq, Set.mem_iInter]]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun k =>
      isClosed_iInter fun l => isClosed_eq (by fun_prop) (by fun_prop)

theorem csb_convex_isAlgCurv (n : ℕ) : Convex ℝ {R : Curv4 n | IsAlgCurv R} := by
  intro R hR S hS a b ha hb hab
  exact isAlgCurv_add (isAlgCurv_smul a hR) (isAlgCurv_smul b hS)

/-- The linear functional whose nonpositivity is `RicPinch` in the direction `v`. -/
noncomputable def csb_ricPinchFun (p : ℝ) (v : Fin n → ℝ) (R : Curv4 n) : ℝ :=
  (p * scalAlg R / (n : ℝ)) * (∑ i, v i * v i) - ∑ i, ∑ j, ric R i j * v i * v j

theorem csb_ricPinch_iff (p : ℝ) (R : Curv4 n) :
    RicPinch p R ↔ ∀ v : Fin n → ℝ, csb_ricPinchFun p v R ≤ 0 := by
  simp only [RicPinch, csb_ricPinchFun]
  constructor <;> intro h v <;> linarith [h v]

theorem csb_continuous_ricPinchFun (p : ℝ) (v : Fin n → ℝ) :
    Continuous fun R : Curv4 n => csb_ricPinchFun p v R := by
  have h1 : Continuous fun R : Curv4 n => (p * scalAlg R / (n : ℝ)) * (∑ i, v i * v i) := by
    have : Continuous fun R : Curv4 n => scalAlg R := by
      simp only [scalAlg]; fun_prop
    fun_prop
  have h2 : Continuous fun R : Curv4 n => ∑ i, ∑ j, ric R i j * v i * v j := by
    simp only [ric]; fun_prop
  exact h1.sub h2

theorem csb_isClosed_ricPinch (p : ℝ) : IsClosed {R : Curv4 n | RicPinch p R} := by
  rw [show {R : Curv4 n | RicPinch p R}
      = ⋂ v : Fin n → ℝ, {R : Curv4 n | csb_ricPinchFun p v R ≤ 0} from by
    ext R
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact csb_ricPinch_iff p R]
  exact isClosed_iInter fun v =>
    IsClosed.preimage (csb_continuous_ricPinchFun p v) isClosed_Iic

lemma csb_sum2_mul (f : Fin n → Fin n → ℝ) (c : ℝ) :
    (∑ i, ∑ j, c * f i j) = c * (∑ i, ∑ j, f i j) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]

theorem csb_convex_ricPinch (p : ℝ) : Convex ℝ {R : Curv4 n | RicPinch p R} := by
  intro R hR S hS a b ha hb hab v
  have h1 := hR v
  have h2 := hS v
  have hs : scalAlg (a • R + b • S) = a * scalAlg R + b * scalAlg S := by
    rw [scalAlg_add_linv, scalAlg_smul_linv, scalAlg_smul_linv]
  have hr : (∑ i, ∑ j, ric (a • R + b • S) i j * v i * v j)
      = a * (∑ i, ∑ j, ric R i j * v i * v j)
        + b * (∑ i, ∑ j, ric S i j * v i * v j) := by
    have hstep : ∀ i j : Fin n,
        ric (a • R + b • S) i j * v i * v j
          = a * (ric R i j * v i * v j) + b * (ric S i j * v i * v j) := by
      intro i j
      rw [ric_add_linv, ric_smul_linv, ric_smul_linv]
      ring
    calc (∑ i, ∑ j, ric (a • R + b • S) i j * v i * v j)
        = ∑ i, ∑ j, (a * (ric R i j * v i * v j) + b * (ric S i j * v i * v j)) :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hstep i j))
      _ = (∑ i, ∑ j, a * (ric R i j * v i * v j))
            + (∑ i, ∑ j, b * (ric S i j * v i * v j)) := by
          simp only [Finset.sum_add_distrib]
      _ = a * (∑ i, ∑ j, ric R i j * v i * v j)
            + b * (∑ i, ∑ j, ric S i j * v i * v j) := by
          rw [csb_sum2_mul (fun i j => ric R i j * v i * v j) a,
            csb_sum2_mul (fun i j => ric S i j * v i * v j) b]
  rw [hs, hr]
  have h3 : p * (a * scalAlg R + b * scalAlg S) / (n : ℝ) * (∑ i, v i * v i)
      = a * (p * scalAlg R / (n : ℝ) * (∑ i, v i * v i))
        + b * (p * scalAlg S / (n : ℝ) * (∑ i, v i * v i)) := by ring
  rw [h3]
  have e1 : a * (p * scalAlg R / (n : ℝ) * (∑ i, v i * v i))
      ≤ a * (∑ i, ∑ j, ric R i j * v i * v j) := mul_le_mul_of_nonneg_left h1 ha
  have e2 : b * (p * scalAlg S / (n : ℝ) * (∑ i, v i * v i))
      ≤ b * (∑ i, ∑ j, ric S i j * v i * v j) := mul_le_mul_of_nonneg_left h2 hb
  linarith

theorem csb_isClosed_dpic (p : ℝ) : IsClosed (Dpic (n := n) p) := by
  have h : Dpic (n := n) p
      = ({R : Curv4 n | IsAlgCurv R} ∩ {R : Curv4 n | InPIC2 R})
        ∩ {R : Curv4 n | RicPinch p R} := by
    ext R; simp only [Dpic, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  rw [h]
  exact (IsClosed.inter (csb_isClosed_isAlgCurv n) (Cone.isClosed_inPIC2 n)).inter
    (csb_isClosed_ricPinch p)

theorem csb_convex_dpic (p : ℝ) : Convex ℝ (Dpic (n := n) p) := by
  have h : Dpic (n := n) p
      = ({R : Curv4 n | IsAlgCurv R} ∩ {R : Curv4 n | InPIC2 R})
        ∩ {R : Curv4 n | RicPinch p R} := by
    ext R; simp only [Dpic, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  rw [h]
  exact ((csb_convex_isAlgCurv n).inter (Cone.convex_inPIC2 n)).inter
    (csb_convex_ricPinch p)

/-- The unit round sphere as a multiple of `id2 ∧ id2`. -/
lemma csb_iso_eq_knProd (n : ℕ) : Iso n = (1 / 2 : ℝ) • knProd (id2 n) (id2 n) := by
  rw [knProd_id2_id2 n, smul_smul]
  norm_num

/-- `ric (Iso n) = (n-1) · id`. -/
lemma csb_ric_iso (n : ℕ) (i j : Fin n) : ric (Iso n) i j = ((n : ℝ) - 1) * id2 n i j := by
  have h := ric_knProd_id2 n (id2 n) i j
  have htr : (∑ k : Fin n, id2 n k k) = (n : ℝ) := by
    simp [id2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [htr] at h
  rw [csb_iso_eq_knProd, ric_smul_linv, h]
  simp only [id2]
  ring

/-- `Iso n` satisfies the Ricci pinching `Ric ≥ (p/n) · scal` for every `p ≤ 1`. -/
lemma csb_ricPinch_iso {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : p ≤ 1) :
    RicPinch (n := n) p (Iso n) := by
  intro v
  have hric : (∑ i : Fin n, ∑ j : Fin n, ric (Iso n) i j * v i * v j)
      = ((n : ℝ) - 1) * (∑ i : Fin n, v i * v i) := by
    have h1 : ∀ i : Fin n, (∑ j : Fin n, ric (Iso n) i j * v i * v j)
        = ((n : ℝ) - 1) * (v i * v i) := by
      intro i
      rw [show (∑ j : Fin n, ric (Iso n) i j * v i * v j)
          = ∑ j : Fin n, (((n : ℝ) - 1) * id2 n i j) * v i * v j from by
        apply Finset.sum_congr rfl; intro j _; rw [csb_ric_iso]]
      rw [show (∑ j : Fin n, (((n : ℝ) - 1) * id2 n i j) * v i * v j)
          = (((n : ℝ) - 1) * v i) * (∑ j : Fin n, id2 n i j * v j) from by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; ring]
      have h3 : (∑ j : Fin n, id2 n i j * v j) = v i := by
        simp only [id2, ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_eq]
        simp
      rw [h3]
      ring
    calc (∑ i : Fin n, ∑ j : Fin n, ric (Iso n) i j * v i * v j)
        = ∑ i : Fin n, ((n : ℝ) - 1) * (v i * v i) :=
          Finset.sum_congr rfl (fun i _ => h1 i)
      _ = ((n : ℝ) - 1) * ∑ i : Fin n, v i * v i := by rw [Finset.mul_sum]
  rw [scalAlg_iso, hric]
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hS : 0 ≤ ∑ i : Fin n, v i * v i := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  have hnm1 : 0 ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hkey : p * ((n : ℝ) * ((n : ℝ) - 1)) / (n : ℝ) = p * ((n : ℝ) - 1) := by
    field_simp
  rw [hkey]
  calc p * ((n : ℝ) - 1) * (∑ i : Fin n, v i * v i)
      = (p * ((n : ℝ) - 1)) * (∑ i : Fin n, v i * v i) := by ring
    _ ≤ (1 * ((n : ℝ) - 1)) * (∑ i : Fin n, v i * v i) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hnm1) hS
    _ = ((n : ℝ) - 1) * (∑ i : Fin n, v i * v i) := by ring

lemma csb_ricPinch_add {p : ℝ} {A B : Curv4 n} (hA : RicPinch p A) (hB : RicPinch p B) :
    RicPinch p (A + B) := by
  intro v
  have h1 := hA v
  have h2 := hB v
  have hs : scalAlg (A + B) = scalAlg A + scalAlg B := scalAlg_add_linv A B
  have hr : (∑ i, ∑ j, ric (A + B) i j * v i * v j)
      = (∑ i, ∑ j, ric A i j * v i * v j) + (∑ i, ∑ j, ric B i j * v i * v j) := by
    have hstep : ∀ i j : Fin n, ric (A + B) i j * v i * v j
        = ric A i j * v i * v j + ric B i j * v i * v j := by
      intro i j; rw [ric_add_linv]; ring
    simp only [hstep, Finset.sum_add_distrib]
  rw [hs, hr]
  have h3 : p * (scalAlg A + scalAlg B) / (n : ℝ) * (∑ i, v i * v i)
      = p * scalAlg A / (n : ℝ) * (∑ i, v i * v i)
        + p * scalAlg B / (n : ℝ) * (∑ i, v i * v i) := by ring
  rw [h3]
  linarith

lemma csb_ricPinch_smul {p c : ℝ} (hc : 0 ≤ c) {A : Curv4 n} (hA : RicPinch p A) :
    RicPinch p (c • A) := by
  intro v
  have h1 := hA v
  have hs : scalAlg (c • A) = c * scalAlg A := scalAlg_smul_linv c A
  have hr : (∑ i, ∑ j, ric (c • A) i j * v i * v j)
      = c * (∑ i, ∑ j, ric A i j * v i * v j) := by
    have hstep : ∀ i j : Fin n, ric (c • A) i j * v i * v j
        = c * (ric A i j * v i * v j) := by
      intro i j; rw [ric_smul_linv]; ring
    simp only [hstep, ← Finset.mul_sum]
  rw [hs, hr]
  have h3 : p * (c * scalAlg A) / (n : ℝ) * (∑ i, v i * v i)
      = c * (p * scalAlg A / (n : ℝ) * (∑ i, v i * v i)) := by ring
  rw [h3]
  exact mul_le_mul_of_nonneg_left h1 hc

/-- The strict `Dpic` cone is contained in the closed one (for `p ≤ 1`). -/
lemma csb_DpicS_subset_Dpic {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : p ≤ 1) {R : Curv4 n}
    (h : R ∈ DpicS (n := n) p) : R ∈ Dpic (n := n) p := by
  obtain ⟨hR, ⟨ε₁, hε₁, hP⟩, ⟨ε₂, hε₂, hQ⟩⟩ := h
  refine ⟨hR, ?_, ?_⟩
  · have : R = (R - ε₁ • Iso n) + ε₁ • Iso n := by abel
    rw [this]
    exact Cone.inPIC2_add hP (Cone.inPIC2_smul (Cone.inPIC2_iso n) hε₁.le)
  · have : R = (R - ε₂ • Iso n) + ε₂ • Iso n := by abel
    rw [this]
    exact csb_ricPinch_add hQ (csb_ricPinch_smul hε₂.le (csb_ricPinch_iso hn hp))

lemma csb_CconeS_subset_Ccone {n : ℕ} (hn : 1 ≤ n) {a b p : ℝ} (hp : p ≤ 1) :
    CconeS (n := n) a b p ⊆ Ccone (n := n) a b p := by
  rintro Y ⟨X, hX, rfl⟩
  exact ⟨X, csb_DpicS_subset_Dpic hn hp hX, rfl⟩

lemma csb_continuous_linv (a b : ℝ) : Continuous fun Y : Curv4 n => linv a b Y := by
  rw [continuous_pi_iff]; intro i
  rw [continuous_pi_iff]; intro j
  rw [continuous_pi_iff]; intro k
  rw [continuous_pi_iff]; intro l
  simp only [linv, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, knProd, ric0, ric, scalAlg, id2]
  fun_prop

lemma csb_ccone_eq {n : ℕ} (a b p : ℝ) (hn : (n : ℝ) ≠ 0)
    (ha : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0) (hb : 1 + ((n : ℝ) - 2) * b ≠ 0) :
    Ccone (n := n) a b p = {R : Curv4 n | IsAlgCurv R ∧ linv a b R ∈ Dpic (n := n) p} := by
  ext R
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨ell_isAlgCurv n a b hS.1, by rw [linv_ell n hn ha hb hS.1]; exact hS⟩
  · rintro ⟨hR, hT⟩
    exact ⟨linv a b R, hT, ell_linv n ha hb hR⟩

lemma csb_isClosed_ccone {n : ℕ} (a b p : ℝ) (hn : (n : ℝ) ≠ 0)
    (ha : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0) (hb : 1 + ((n : ℝ) - 2) * b ≠ 0) :
    IsClosed (Ccone (n := n) a b p) := by
  rw [csb_ccone_eq a b p hn ha hb]
  exact (csb_isClosed_isAlgCurv n).inter
    (IsClosed.preimage (csb_continuous_linv a b) (csb_isClosed_dpic p))

lemma csb_convex_ccone {n : ℕ} (a b p : ℝ) (hn : (n : ℝ) ≠ 0)
    (ha : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0) (hb : 1 + ((n : ℝ) - 2) * b ≠ 0) :
    Convex ℝ (Ccone (n := n) a b p) := by
  rw [csb_ccone_eq a b p hn ha hb]
  intro R hR S hS u v hu hv huv
  obtain ⟨h1, h2⟩ := hR
  obtain ⟨h3, h4⟩ := hS
  refine ⟨isAlgCurv_add (isAlgCurv_smul u h1) (isAlgCurv_smul v h3), ?_⟩
  rw [linv_add, linv_smul, linv_smul]
  exact csb_convex_dpic p h2 h4 hu hv huv

lemma csb_natCast_ne_zero {n : ℕ} (hn : 2 ≤ n) : (n : ℝ) ≠ 0 := by
  have : (0 : ℕ) < n := by omega
  exact_mod_cast (ne_of_gt this)

lemma csb_denom_a (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) :
    1 + 2 * ((n : ℝ) - 1) * chatA n s ≠ 0 := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have ha : 0 ≤ chatA n s := chatA_nonneg hn hs.le
  have : (0 : ℝ) < 1 + 2 * ((n : ℝ) - 1) * chatA n s := by nlinarith
  exact ne_of_gt this

lemma csb_denom_b (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) :
    1 + ((n : ℝ) - 2) * s ≠ 0 := by
  have h2 : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
  have : (0 : ℝ) < 1 + ((n : ℝ) - 2) * s := by nlinarith
  exact ne_of_gt this

lemma csb_denom_a2 (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) :
    1 + 2 * ((n : ℝ) - 1) * s ≠ 0 := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have : (0 : ℝ) < 1 + 2 * ((n : ℝ) - 1) * s := by nlinarith
  exact ne_of_gt this

lemma csb_denom_b2 (n : ℕ) (hn : 2 ≤ n) :
    1 + ((n : ℝ) - 2) * (1 / 2 : ℝ) ≠ 0 := by
  have h2 : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
  have : (0 : ℝ) < 1 + ((n : ℝ) - 2) * (1 / 2 : ℝ) := by nlinarith
  exact ne_of_gt this

theorem csb_isClosed_chat (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) :
    IsClosed (Chat n s) := by
  by_cases h : s ≤ 1 / 2
  · rw [Chat_eq_Ccone n h]
    exact csb_isClosed_ccone (chatA n s) s (chatP n s) (csb_natCast_ne_zero hn)
      (csb_denom_a n hn hs) (csb_denom_b n hn hs)
  · have hChat : Chat n s = Ccone (n := n) s (1 / 2) (1 - 4 / ((n : ℝ) - 2 + 8 * s)) := by
      rw [Chat, if_neg h]
    rw [hChat]
    exact csb_isClosed_ccone s (1 / 2) (1 - 4 / ((n : ℝ) - 2 + 8 * s))
      (csb_natCast_ne_zero hn) (csb_denom_a2 n hn hs) (csb_denom_b2 n hn)

theorem csb_convex_chat (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) :
    Convex ℝ (Chat n s) := by
  by_cases h : s ≤ 1 / 2
  · rw [Chat_eq_Ccone n h]
    exact csb_convex_ccone (chatA n s) s (chatP n s) (csb_natCast_ne_zero hn)
      (csb_denom_a n hn hs) (csb_denom_b n hn hs)
  · have hChat : Chat n s = Ccone (n := n) s (1 / 2) (1 - 4 / ((n : ℝ) - 2 + 8 * s)) := by
      rw [Chat, if_neg h]
    rw [hChat]
    exact csb_convex_ccone s (1 / 2) (1 - 4 / ((n : ℝ) - 2 + 8 * s))
      (csb_natCast_ne_zero hn) (csb_denom_a2 n hn hs) (csb_denom_b2 n hn)

/-- The strict cone `ChatS n s` is contained in the closed cone `Chat n s`. -/
lemma csb_chatS_subset_chat (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) :
    ChatS n s ⊆ Chat n s := by
  intro R hR
  by_cases h : s ≤ 1 / 2
  · have hmem : R ∈ CconeS (n := n) (chatA n s) s (chatP n s) := by
      rw [ChatS, if_pos h] at hR
      exact hR
    have hres : R ∈ Ccone (n := n) (chatA n s) s (chatP n s) :=
      csb_CconeS_subset_Ccone (by omega : 1 ≤ n) (le_of_lt (chatP_lt_one hn s)) hmem
    rwa [Chat_eq_Ccone n h]
  · have hmem : R ∈ CconeS (n := n) s (1 / 2) (1 - 4 / ((n : ℝ) - 2 + 8 * s)) := by
      rw [ChatS, if_neg h] at hR
      exact hR
    have hp : 1 - 4 / ((n : ℝ) - 2 + 8 * s) ≤ 1 := by
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hden : 0 < (n : ℝ) - 2 + 8 * s := by linarith
      have : 0 ≤ 4 / ((n : ℝ) - 2 + 8 * s) := div_nonneg (by norm_num) hden.le
      linarith
    have hres : R ∈ Ccone (n := n) s (1 / 2) (1 - 4 / ((n : ℝ) - 2 + 8 * s)) :=
      csb_CconeS_subset_Ccone (by omega : 1 ≤ n) hp hmem
    rwa [Chat, if_neg h]

/-! ## 2. Elementary facts about the cones -/

lemma isAlgCurv_zero' (n : ℕ) : IsAlgCurv (0 : Curv4 n) := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp

lemma inPIC2_zero' (n : ℕ) : InPIC2 (0 : Curv4 n) := by
  intro x y z w
  simp [R4]

lemma ricPinch_zero' (n : ℕ) (p : ℝ) : RicPinch p (0 : Curv4 n) := by
  intro v
  simp [ric, scalAlg]

lemma ric0_zero' (n : ℕ) : ric0 (0 : Curv4 n) = 0 := by
  funext i j
  simp [ric0, ric, scalAlg]

lemma knProd_zero_left' (n : ℕ) : knProd (0 : Fin n → Fin n → ℝ) (id2 n) = 0 := by
  funext i j k l
  simp [knProd]

lemma scalAlg_zero' (n : ℕ) : scalAlg (0 : Curv4 n) = 0 := by simp [scalAlg]

lemma linv_zero' (n : ℕ) (a b : ℝ) : linv a b (0 : Curv4 n) = 0 := by
  rw [linv, ric0_zero', knProd_zero_left', scalAlg_zero']
  simp

lemma ell_zero' (n : ℕ) (a b : ℝ) : ell a b (0 : Curv4 n) = 0 := by
  rw [ell, ric0_zero', knProd_zero_left', scalAlg_zero']
  simp

lemma chat_zero_mem (n : ℕ) (hn : 2 ≤ n) (s : ℝ) : (0 : Curv4 n) ∈ Chat n s := by
  rw [chat_eq_Ccone_param n]
  refine ⟨0, ⟨isAlgCurv_zero' n, inPIC2_zero' n, ricPinch_zero' n _⟩, ell_zero' n _ _⟩

lemma chat_isAlgCurv (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) {R : Curv4 n}
    (hR : R ∈ Chat n s) : IsAlgCurv R := by
  rw [chat_eq_Ccone_param n] at hR
  obtain ⟨S, hS, rfl⟩ := hR
  exact ell_isAlgCurv n _ _ hS.1

lemma chat_scalAlg_nonneg (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) {X : Curv4 n}
    (hX : X ∈ Chat n s) : 0 ≤ scalAlg X := by
  rw [chat_eq_Ccone_param n] at hX
  obtain ⟨S, hS, rfl⟩ := hX
  rw [scalAlg_ell_of_ne n _ _ (by positivity) hS.1]
  have h1 : (0 : ℝ) ≤ 1 + 2 * ((n : ℝ) - 1) * chatAA n s := by
    have := chatAA_nonneg n hn hs.le
    have h2 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    nlinarith
  exact mul_nonneg h1 ((inPIC2_metric_basic n).2.2 S hS.2.1)

lemma chat_scalAlg_eq_zero (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) {X : Curv4 n}
    (hX : X ∈ Chat n s) (h0 : scalAlg X = 0) : X = 0 := by
  rw [chat_eq_Ccone_param n] at hX
  obtain ⟨S, hS, rfl⟩ := hX
  have hS0 : scalAlg S = 0 := by
    rw [scalAlg_ell_of_ne n _ _ (by positivity) hS.1] at h0
    exact (mul_eq_zero.mp h0).resolve_left (chatAA_denom n hn hs.le)
  rw [(inPIC2_comp_bound n).2 S hS.2.1 hS0, ell_zero']

lemma chat_scalAlg_pos_of_ne (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) {X : Curv4 n}
    (hX : X ∈ Chat n s) (hX0 : X ≠ 0) : 0 < scalAlg X :=
  lt_of_le_of_ne (chat_scalAlg_nonneg n hn hs hX)
    (fun h => hX0 (chat_scalAlg_eq_zero n hn hs hX h.symm))

lemma chat_smul_mem (n : ℕ) (hn : 2 ≤ n) {s c : ℝ} (hc : 0 ≤ c) {R : Curv4 n}
    (hR : R ∈ Chat n s) : c • R ∈ Chat n s := by
  rw [chat_eq_Ccone_param n] at hR ⊢
  obtain ⟨S, hS, rfl⟩ := hR
  exact ⟨c • S, ⟨isAlgCurv_smul c hS.1, Cone.inPIC2_smul hS.2.1 hc, csb_ricPinch_smul hc hS.2.2⟩,
    by rw [ell_smul]⟩

lemma chat_iso_mem (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) : Iso n ∈ Chat n s := by
  have h1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have ha : (0 : ℝ) < 1 + 2 * ((n : ℝ) - 1) * chatAA n s := by
    have := chatAA_nonneg n hn hs.le
    nlinarith
  have hlam : 0 ≤ 1 / (1 + 2 * ((n : ℝ) - 1) * chatAA n s) := div_nonneg (by norm_num) ha.le
  rw [chat_eq_Ccone_param n]
  refine ⟨(1 / (1 + 2 * ((n : ℝ) - 1) * chatAA n s)) • Iso n, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact isAlgCurv_smul _ (Iso_algCurv n)
  · exact Cone.inPIC2_smul (Cone.inPIC2_iso n) hlam
  · exact csb_ricPinch_smul hlam
      (csb_ricPinch_iso (by omega) (le_of_lt (chatPP_lt_one n hn hs)))
  · rw [← cm_linv_iso (n := n) (by omega) (chatAA_denom n hn hs.le)]
    exact ell_linv n (chatAA_denom n hn hs.le) (chatBB_denom n hn hs.le) (Iso_algCurv n)

/-! ## 3. Componentwise bounds for `ell` and `linv` -/

lemma abs_ric_le (X : Curv4 n) (i j : Fin n) : |ric X i j| ≤ (n : ℝ) * ‖X‖ := by
  rw [ric]
  calc |∑ k, X k i k j| ≤ ∑ k, ‖X‖ :=
        le_trans (Finset.abs_sum_le_sum_abs _ _)
          (Finset.sum_le_sum fun k _ => cm_abs_component_le_norm X k i k j)
    _ = (n : ℝ) * ‖X‖ := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma abs_mul_le_mul {a b A B : ℝ} (hA : |a| ≤ A) (hB : |b| ≤ B) (hA0 : 0 ≤ A) :
    |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul hA hB (abs_nonneg _) hA0

lemma abs_knProd_aux (a b c d : ℝ) : |a - b - c + d| ≤ |a| + |b| + |c| + |d| := by
  rw [abs_le]
  have h1 := neg_abs_le a
  have h2 := neg_abs_le b
  have h3 := neg_abs_le c
  have h4 := neg_abs_le d
  have h5 := le_abs_self a
  have h6 := le_abs_self b
  have h7 := le_abs_self c
  have h8 := le_abs_self d
  constructor <;> linarith

lemma abs_ric0_le (hn : 2 ≤ n) (X : Curv4 n) (i j : Fin n) :
    |ric0 X i j| ≤ 2 * (n : ℝ) * ‖X‖ := by
  have h1 := abs_ric_le X i j
  have h2 := cm_abs_scalAlg_le X
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hid : |id2 n i j| ≤ 1 := by
    by_cases h : i = j <;> simp [id2, h]
  have h3 : |scalAlg X / (n : ℝ) * id2 n i j| ≤ (n : ℝ) * ‖X‖ := by
    have h4 : |scalAlg X / (n : ℝ)| ≤ (n : ℝ) * ‖X‖ := by
      rw [abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
      nlinarith
    calc |scalAlg X / (n : ℝ) * id2 n i j| ≤ ((n : ℝ) * ‖X‖) * 1 :=
          abs_mul_le_mul h4 hid (by positivity)
      _ = (n : ℝ) * ‖X‖ := by ring
  rw [ric0, abs_le]
  have h5 := (abs_le.mp h1)
  have h6 := (abs_le.mp h3)
  constructor <;> linarith

lemma abs_knProd_ric0_id2_le (hn : 2 ≤ n) (X : Curv4 n) (i j k l : Fin n) :
    |knProd (ric0 X) (id2 n) i j k l| ≤ 8 * (n : ℝ) * ‖X‖ := by
  have h : ∀ p q : Fin n, |ric0 X p q| ≤ 2 * (n : ℝ) * ‖X‖ := fun p q => abs_ric0_le hn X p q
  have hid : ∀ p q : Fin n, |id2 n p q| ≤ 1 := by
    intro p q
    by_cases hpq : p = q <;> simp [id2, hpq]
  have h1 : |ric0 X i k * id2 n j l| ≤ 2 * (n : ℝ) * ‖X‖ := by
    have := abs_mul_le_mul (h i k) (hid j l) (by positivity)
    rwa [mul_one] at this
  have h2 : |ric0 X i l * id2 n j k| ≤ 2 * (n : ℝ) * ‖X‖ := by
    have := abs_mul_le_mul (h i l) (hid j k) (by positivity)
    rwa [mul_one] at this
  have h3 : |ric0 X j k * id2 n i l| ≤ 2 * (n : ℝ) * ‖X‖ := by
    have := abs_mul_le_mul (h j k) (hid i l) (by positivity)
    rwa [mul_one] at this
  have h4 : |ric0 X j l * id2 n i k| ≤ 2 * (n : ℝ) * ‖X‖ := by
    have := abs_mul_le_mul (h j l) (hid i k) (by positivity)
    rwa [mul_one] at this
  rw [knProd]
  have h5 := abs_knProd_aux (ric0 X i k * id2 n j l) (ric0 X i l * id2 n j k)
    (ric0 X j k * id2 n i l) (ric0 X j l * id2 n i k)
  linarith

lemma abs_knProd_id2_id2_le (n : ℕ) (i j k l : Fin n) :
    |knProd (id2 n) (id2 n) i j k l| ≤ 4 := by
  have hid : ∀ p q : Fin n, |id2 n p q| ≤ 1 := by
    intro p q
    by_cases hpq : p = q <;> simp [id2, hpq]
  have h1 : |id2 n i k * id2 n j l| ≤ 1 := by
    have := abs_mul_le_mul (hid i k) (hid j l) (by norm_num)
    rwa [mul_one] at this
  have h2 : |id2 n i l * id2 n j k| ≤ 1 := by
    have := abs_mul_le_mul (hid i l) (hid j k) (by norm_num)
    rwa [mul_one] at this
  have h3 : |id2 n j k * id2 n i l| ≤ 1 := by
    have := abs_mul_le_mul (hid j k) (hid i l) (by norm_num)
    rwa [mul_one] at this
  have h4 : |id2 n j l * id2 n i k| ≤ 1 := by
    have := abs_mul_le_mul (hid j l) (hid i k) (by norm_num)
    rwa [mul_one] at this
  rw [knProd]
  have h5 := abs_knProd_aux (id2 n i k * id2 n j l) (id2 n i l * id2 n j k)
    (id2 n j k * id2 n i l) (id2 n j l * id2 n i k)
  linarith

lemma ell_comp_bound (n : ℕ) (hn : 2 ≤ n) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (S : Curv4 n) (i j k l : Fin n) :
    |ell a b S i j k l| ≤ (1 + 8 * (n : ℝ) * b + 4 * (n : ℝ) * a) * ‖S‖ := by
  have hS : |S i j k l| ≤ ‖S‖ := cm_abs_component_le_norm S i j k l
  have hK1 := abs_knProd_ric0_id2_le hn S i j k l
  have hK2 := abs_knProd_id2_id2_le n i j k l
  have hsc : |scalAlg S| ≤ (n : ℝ) ^ 2 * ‖S‖ := cm_abs_scalAlg_le S
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hb1 : |b * knProd (ric0 S) (id2 n) i j k l| ≤ 8 * (n : ℝ) * b * ‖S‖ := by
    calc |b * knProd (ric0 S) (id2 n) i j k l| ≤ b * (8 * (n : ℝ) * ‖S‖) :=
          abs_mul_le_mul (le_of_eq (abs_of_nonneg hb)) hK1 (by positivity)
      _ = 8 * (n : ℝ) * b * ‖S‖ := by ring
  have hb2 : |(a / (n : ℝ) * scalAlg S) * knProd (id2 n) (id2 n) i j k l|
      ≤ 4 * (n : ℝ) * a * ‖S‖ := by
    have ha1 : |a / (n : ℝ) * scalAlg S| ≤ a * (n : ℝ) * ‖S‖ := by
      have h4 : |a / (n : ℝ)| ≤ a / (n : ℝ) := le_of_eq (abs_of_nonneg (div_nonneg ha hn0.le))
      calc |a / (n : ℝ) * scalAlg S| ≤ (a / (n : ℝ)) * ((n : ℝ) ^ 2 * ‖S‖) :=
            abs_mul_le_mul h4 hsc (by positivity)
        _ = a * (n : ℝ) * ‖S‖ := by field_simp
    calc |(a / (n : ℝ) * scalAlg S) * knProd (id2 n) (id2 n) i j k l|
        ≤ (a * (n : ℝ) * ‖S‖) * 4 := abs_mul_le_mul ha1 hK2 (by positivity)
      _ = 4 * (n : ℝ) * a * ‖S‖ := by ring
  simp only [ell, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [abs_le]
  have h1 := (abs_le.mp hS)
  have h2 := (abs_le.mp hb1)
  have h3 := (abs_le.mp hb2)
  constructor <;> linarith

lemma linv_comp_bound (n : ℕ) (hn : 2 ≤ n) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (Y : Curv4 n) (i j k l : Fin n) :
    |linv a b Y i j k l| ≤ (1 + 8 * (n : ℝ) * b + 4 * (n : ℝ) * a) * ‖Y‖ := by
  have hY : |Y i j k l| ≤ ‖Y‖ := cm_abs_component_le_norm Y i j k l
  have hK1 := abs_knProd_ric0_id2_le hn Y i j k l
  have hK2 := abs_knProd_id2_id2_le n i j k l
  have hsc : |scalAlg Y| ≤ (n : ℝ) ^ 2 * ‖Y‖ := cm_abs_scalAlg_le Y
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h1n : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h2n : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
  have hcb0 : 0 ≤ b / (1 + ((n : ℝ) - 2) * b) := div_nonneg hb (by nlinarith)
  have hcb : b / (1 + ((n : ℝ) - 2) * b) ≤ b := by
    have hden : (0 : ℝ) < 1 + ((n : ℝ) - 2) * b := by nlinarith
    rw [div_le_iff₀ hden]
    have hk : 0 ≤ ((n : ℝ) - 2) * b := mul_nonneg h2n hb
    nlinarith
  have hca0 : 0 ≤ (a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) :=
    div_nonneg (div_nonneg ha hn0.le) (by nlinarith)
  have hca : (a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) ≤ a / (n : ℝ) := by
    have hden : (0 : ℝ) < 1 + 2 * ((n : ℝ) - 1) * a := by nlinarith
    rw [div_le_iff₀ hden]
    have ht : 0 ≤ a / (n : ℝ) := div_nonneg ha hn0.le
    have hk : 0 ≤ 2 * ((n : ℝ) - 1) * a := by nlinarith
    have hm := mul_nonneg ht hk
    calc a / (n : ℝ) ≤ a / (n : ℝ) + a / (n : ℝ) * (2 * ((n : ℝ) - 1) * a) := by linarith
      _ = a / (n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * a) := by ring
  have hb1 : |b / (1 + ((n : ℝ) - 2) * b) * knProd (ric0 Y) (id2 n) i j k l|
      ≤ 8 * (n : ℝ) * b * ‖Y‖ := by
    have hcb' : |b / (1 + ((n : ℝ) - 2) * b)| ≤ b := by
      rw [abs_of_nonneg hcb0]; exact hcb
    calc |b / (1 + ((n : ℝ) - 2) * b) * knProd (ric0 Y) (id2 n) i j k l|
        ≤ b * (8 * (n : ℝ) * ‖Y‖) := abs_mul_le_mul hcb' hK1 (by positivity)
      _ = 8 * (n : ℝ) * b * ‖Y‖ := by ring
  have hb2 : |(a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg Y
      * knProd (id2 n) (id2 n) i j k l| ≤ 4 * (n : ℝ) * a * ‖Y‖ := by
    have ha1 : |(a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg Y|
        ≤ a * (n : ℝ) * ‖Y‖ := by
      have hca' : |(a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a)| ≤ a / (n : ℝ) := by
        rw [abs_of_nonneg hca0]; exact hca
      calc |(a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg Y|
          ≤ (a / (n : ℝ)) * ((n : ℝ) ^ 2 * ‖Y‖) := abs_mul_le_mul hca' hsc (by positivity)
        _ = a * (n : ℝ) * ‖Y‖ := by field_simp
    calc |(a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg Y
        * knProd (id2 n) (id2 n) i j k l| ≤ (a * (n : ℝ) * ‖Y‖) * 4 :=
          abs_mul_le_mul ha1 hK2 (by positivity)
      _ = 4 * (n : ℝ) * a * ‖Y‖ := by ring
  simp only [linv, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [abs_le]
  have h1 := (abs_le.mp hY)
  have h2 := (abs_le.mp hb1)
  have h3 := (abs_le.mp hb2)
  constructor <;> linarith

lemma ell_norm_le (n : ℕ) (hn : 2 ≤ n) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (S : Curv4 n) :
    ‖ell a b S‖ ≤ (1 + 8 * (n : ℝ) * b + 4 * (n : ℝ) * a) * ‖S‖ := by
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.mpr fun i => ?_
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.mpr fun j => ?_
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.mpr fun k => ?_
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.mpr fun l => ?_
  rw [Real.norm_eq_abs]
  exact ell_comp_bound n hn a b ha hb S i j k l

lemma linv_norm_le (n : ℕ) (hn : 2 ≤ n) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (Y : Curv4 n) :
    ‖linv a b Y‖ ≤ (1 + 8 * (n : ℝ) * b + 4 * (n : ℝ) * a) * ‖Y‖ := by
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.mpr fun i => ?_
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.mpr fun j => ?_
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.mpr fun k => ?_
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.mpr fun l => ?_
  rw [Real.norm_eq_abs]
  exact linv_comp_bound n hn a b ha hb Y i j k l

/-! ## 4. Uniform norm bound on the cones of a compact parameter interval -/

theorem chat_norm_le_scalAlg_uniform (n : ℕ) (hn : 2 ≤ n) {s₀ T : ℝ} (hs₀ : 0 < s₀)
    (hT : s₀ ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, s₀ ≤ s → s ≤ T → ∀ X : Curv4 n,
      X ∈ Chat n s → ‖X‖ ≤ C * scalAlg X := by
  obtain ⟨C₀, hC₀⟩ := (inPIC2_comp_bound n).1
  have hC₁ : (0 : ℝ) ≤ max C₀ 0 := le_max_right _ _
  have hC₀' : ∀ R : Curv4 n, InPIC2 R → ∀ i j k l : Fin n,
      |R i j k l| ≤ max C₀ 0 * scalAlg R := by
    intro R hR i j k l
    have hsc : 0 ≤ scalAlg R := (inPIC2_metric_basic n).2.2 R hR
    exact (hC₀ R hR i j k l).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hsc)
  refine ⟨(1 + 8 * (n : ℝ) * (1 / 2) + 4 * (n : ℝ) * max (1 / 2 : ℝ) T) * max C₀ 0,
    by positivity, ?_⟩
  intro s hs₀s hsT X hX
  rw [chat_eq_Ccone_param n] at hX
  obtain ⟨S, hS, rfl⟩ := hX
  have hs : (0 : ℝ) ≤ s := le_trans hs₀.le hs₀s
  have ha : 0 ≤ chatAA n s := chatAA_nonneg n hn hs
  have hb : 0 ≤ chatBB s := chatBB_nonneg hs
  have h1 : ‖ell (chatAA n s) (chatBB s) S‖
      ≤ (1 + 8 * (n : ℝ) * chatBB s + 4 * (n : ℝ) * chatAA n s) * ‖S‖ :=
    ell_norm_le n hn _ _ ha hb S
  have h8 : 0 ≤ scalAlg S := (inPIC2_metric_basic n).2.2 S hS.2.1
  have h2 : ‖S‖ ≤ max C₀ 0 * scalAlg S := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg hC₁ h8)]
    intro i
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg hC₁ h8)]
    intro j
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg hC₁ h8)]
    intro k
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg hC₁ h8)]
    intro l
    rw [Real.norm_eq_abs]
    exact hC₀' S hS.2.1 i j k l
  have h3 : scalAlg S ≤ scalAlg (ell (chatAA n s) (chatBB s) S) := by
    rw [scalAlg_ell_of_ne n _ _ (by positivity) hS.1]
    have h5 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have h6 : (1 : ℝ) ≤ 1 + 2 * ((n : ℝ) - 1) * chatAA n s := by nlinarith
    nlinarith [(inPIC2_metric_basic n).2.2 S hS.2.1]
  have h5 : (1 + 8 * (n : ℝ) * chatBB s + 4 * (n : ℝ) * chatAA n s)
      ≤ (1 + 8 * (n : ℝ) * (1 / 2) + 4 * (n : ℝ) * max (1 / 2 : ℝ) T) := by
    have h6 := chatBB_le_half s
    have h7 := chatAA_le n hn hsT
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have h9 : 0 ≤ scalAlg (ell (chatAA n s) (chatBB s) S) := le_trans h8 h3
  calc ‖ell (chatAA n s) (chatBB s) S‖
      ≤ (1 + 8 * (n : ℝ) * chatBB s + 4 * (n : ℝ) * chatAA n s) * ‖S‖ := h1
    _ ≤ (1 + 8 * (n : ℝ) * (1 / 2) + 4 * (n : ℝ) * max (1 / 2 : ℝ) T) * ‖S‖ :=
        mul_le_mul_of_nonneg_right h5 (norm_nonneg S)
    _ ≤ (1 + 8 * (n : ℝ) * (1 / 2) + 4 * (n : ℝ) * max (1 / 2 : ℝ) T)
          * (max C₀ 0 * scalAlg S) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ (1 + 8 * (n : ℝ) * (1 / 2) + 4 * (n : ℝ) * max (1 / 2 : ℝ) T)
          * (max C₀ 0 * scalAlg (ell (chatAA n s) (chatBB s) S)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hC₁) (by positivity)
    _ = (1 + 8 * (n : ℝ) * (1 / 2) + 4 * (n : ℝ) * max (1 / 2 : ℝ) T) * max C₀ 0
          * scalAlg (ell (chatAA n s) (chatBB s) S) := by ring

/-! ## 5. The clamped inverse `chatLinv` -/

/-- The inverse of the Böhm–Wilking transform at the parameters `(chatAA n s, chatBB s)`, with
the parameters clamped at `0` in the two denominators so that the expression is meaningful and
continuous for *all* `s`.  For `s ≥ 0` it equals `linv (chatAA n s) (chatBB s)`. -/
noncomputable def chatLinv (n : ℕ) (s : ℝ) (Y : Curv4 n) : Curv4 n :=
  Y - (max (chatBB s) 0 / (1 + ((n : ℝ) - 2) * max (chatBB s) 0)) • knProd (ric0 Y) (id2 n)
    - ((max (chatAA n s) 0 / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * max (chatAA n s) 0)
        * scalAlg Y) • knProd (id2 n) (id2 n)

lemma chatLinv_eq_linv (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 ≤ s) (Y : Curv4 n) :
    chatLinv n s Y = linv (chatAA n s) (chatBB s) Y := by
  rw [chatLinv, linv, max_eq_left (chatBB_nonneg hs), max_eq_left (chatAA_nonneg n hn hs)]

lemma continuous_scalAlg' (n : ℕ) : Continuous fun X : Curv4 n => scalAlg X := by
  simp only [scalAlg]
  fun_prop

lemma continuous_knProd_ric0_id2 (n : ℕ) :
    Continuous fun Y : Curv4 n => knProd (ric0 Y) (id2 n) := by
  rw [continuous_pi_iff]; intro i
  rw [continuous_pi_iff]; intro j
  rw [continuous_pi_iff]; intro k
  rw [continuous_pi_iff]; intro l
  simp only [knProd, ric0, ric, scalAlg, id2]
  fun_prop

lemma continuous_chatLinv (n : ℕ) (hn : 2 ≤ n) :
    Continuous fun q : ℝ × Curv4 n => chatLinv n q.1 q.2 := by
  have h2 : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
  have h1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hb : Continuous fun q : ℝ × Curv4 n =>
      max (chatBB q.1) 0 / (1 + ((n : ℝ) - 2) * max (chatBB q.1) 0) := by
    refine Continuous.div ?_ ?_ (fun q => ?_)
    · exact continuous_chatBB.max continuous_const |>.comp continuous_fst
    · exact continuous_const.add (continuous_const.mul
        (continuous_chatBB.max continuous_const |>.comp continuous_fst))
    · exact ne_of_gt (by nlinarith [le_max_right (chatBB q.1) 0])
  have ha : Continuous fun q : ℝ × Curv4 n =>
      (max (chatAA n q.1) 0 / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * max (chatAA n q.1) 0)
        * scalAlg q.2 := by
    refine Continuous.mul (Continuous.div ?_ ?_ (fun q => ?_)) (continuous_scalAlg' n |>.comp continuous_snd)
    · exact Continuous.div ((continuous_chatAA n hn).max continuous_const |>.comp continuous_fst)
        continuous_const (fun q => by
          have hn0 : (0 : ℕ) < n := by omega
          exact_mod_cast (ne_of_gt hn0))
    · exact continuous_const.add (continuous_const.mul
        ((continuous_chatAA n hn).max continuous_const |>.comp continuous_fst))
    · exact ne_of_gt (by nlinarith [le_max_right (chatAA n q.1) 0])
  have h : (fun q : ℝ × Curv4 n => chatLinv n q.1 q.2)
      = fun q : ℝ × Curv4 n => q.2 - (max (chatBB q.1) 0 / (1 + ((n : ℝ) - 2) * max (chatBB q.1) 0))
            • knProd (ric0 q.2) (id2 n)
          - ((max (chatAA n q.1) 0 / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * max (chatAA n q.1) 0)
              * scalAlg q.2) • knProd (id2 n) (id2 n) := by
    funext q
    rw [chatLinv]
  rw [h]
  exact (continuous_snd.sub (hb.smul ((continuous_knProd_ric0_id2 n).comp continuous_snd))).sub
    (ha.smul continuous_const)


/-! ## 5b. Elementary facts about Hamilton's reaction term `Q` -/

lemma csb_Q_zero (n : ℕ) : Q (0 : Curv4 n) = 0 := by
  funext i j k l
  simp [Q]

lemma csb_Q_smul (c : ℝ) (R : Curv4 n) : Q (c • R) = (c * c) • Q R := by
  funext i j k l
  simp only [Q, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro q _
  ring

end Work.Diff.Alg.Pinch
