import Mathlib
import Submission.Work.Diff.Alg.Pinch.RoomAux.Strict
import Submission.Work.Diff.Alg.Pinch.ChatShiftStrictDefs
import Submission.Work.Diff.Alg.Pinch.Chat_shift_base
import Submission.Work.Diff.Alg.Pinch.Chat_family_structure
import Submission.Work.Diff.Alg.Pinch.Chat_linv_bound
import Submission.Work.Diff.Alg.Pinch.Q_shift_iso
import Submission.Work.Diff.Alg.Pinch.Chat_margin
import Submission.Work.Diff.Alg.Pinch.ric0_mulVec_of_tight
import Submission.Work.Diff.Alg.Pinch.ric0Frob2_le
import Submission.Work.Diff.Alg.Pinch.ChatT_strict_pic_b
import Submission.Work.Diff.Alg.Pinch.ChatT_strict_pic_a
import Submission.Work.Diff.Alg.Pinch.ChatT_pic_b_v2
import Submission.Work.Diff.Alg.Pinch.ricForm_X_strict_at_tight_a
import Submission.Work.Diff.Alg.Pinch.Chat_exhaust
import Submission.Work.Diff.PP.Q_smul
import Submission.Work.Diff.Alg.Pinch.Q_iso

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniform shifted strictness for the Brendle–Schoen pinching family

The target `Work.Diff.Alg.Pinch.chat_shift_strict`: the pointwise strictness input
`ShiftStrict n s ĉ X` of the one-step lemmas `ChatT_one_step_pic`
(`Diff/Alg/Pinch/ChatT_one_step_pic.lean`) and `RicPinch_one_step_of_strict` holds *uniformly*
in the parameter `s ≥ ε` for all sufficiently small `ĉ > 0`.

## The route

For `X ∈ Ĉ(s)` with `scalAlg X = 1` write `X = ell a b S` with
`S = chatLinv n s X ∈ Dpic p` the preimage, `σ = scalAlg S = 1/(1 + 2(n-1)a)`.  The shifted
reaction direction is

`chatLinv n s (Q (X - ĉ • Iso n)) = W₀ + ĉ² (2(n-1)σ) • Iso n - 2ĉ • M`,

`W₀ = linv a b (Q X)`, `M = linv a b (knProd (ric X) (id2 n))` (bilinearity of `Q`
(`Q_add_polarize`, `BQ_iso`) and linearity of `linv`).

Both forms `ricMarg · p v` and `Q2P.EFun · x y z w` are linear in the tensor, and the pointwise
Böhm–Wilking strictness (in its quantitative form) bounds the first term from below on the tight
(resp. degenerate) directions, while `‖M‖ ≤ σ K_E` bounds the perturbation.  An explicit
`ĉ₀ > 0`, uniform in `s ≥ ε`, is then obtained by elementary arithmetic.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## 1. The Ricci-form margin and its linearity -/

/-- The Ricci-form margin `ricMarg T p v = ric T (v,v) - (p · scal T / n) ‖v‖²`.  The first
conjunct of `ShiftStrict` asks for `ricMarg S p v = 0 → 0 < ricMarg W p v`. -/
noncomputable def ricMarg (T : Curv4 n) (p : ℝ) (v : Fin n → ℝ) : ℝ :=
  qform (ric T) v - (p * scalAlg T / (n : ℝ)) * qform (id2 n) v

lemma qform_id2_eq (v : Fin n → ℝ) : qform (id2 n) v = ∑ i, v i * v i := by
  simp only [qform, id2]
  exact sum_delta_sq v

lemma ricMarg_eq (T : Curv4 n) (p : ℝ) (v : Fin n → ℝ) :
    ricMarg T p v = (∑ i, ∑ j, ric T i j * v i * v j)
      - (p * scalAlg T / (n : ℝ)) * (∑ i, v i * v i) := by
  rw [ricMarg, qform_id2_eq]
  rfl

lemma ricMarg_add (T T' : Curv4 n) (p : ℝ) (v : Fin n → ℝ) :
    ricMarg (T + T') p v = ricMarg T p v + ricMarg T' p v := by
  have hric : ric (T + T') = ric T + ric T' :=
    funext fun i => funext fun j => ric_add_linv T T' i j
  rw [ricMarg, ricMarg, ricMarg, hric, scalAlg_add_linv, qform_add]
  ring

lemma ricMarg_smul (c : ℝ) (T : Curv4 n) (p : ℝ) (v : Fin n → ℝ) :
    ricMarg (c • T) p v = c * ricMarg T p v := by
  have hric : ric (c • T) = c • ric T :=
    funext fun i => funext fun j => ric_smul_linv c T i j
  rw [ricMarg, ricMarg, hric, scalAlg_smul_linv, qform_smul]
  ring

lemma ricMarg_add_smul (T T' : Curv4 n) (p c : ℝ) (v : Fin n → ℝ) :
    ricMarg (T + c • T') p v = ricMarg T p v + c * ricMarg T' p v := by
  rw [ricMarg_add, ricMarg_smul]

/-- `ricMarg` of the round sphere. -/
lemma ricMarg_Iso (hn : 2 ≤ n) (p : ℝ) (v : Fin n → ℝ) :
    ricMarg (Iso n) p v = ((n : ℝ) - 1) * (1 - p) * (∑ i, v i * v i) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  rw [ricMarg_eq]
  have h1 : (∑ i, ∑ j, ric (Iso n) i j * v i * v j) = ((n : ℝ) - 1) * (∑ i, v i * v i) := by
    have h2 : (∑ i, ∑ j, ric (Iso n) i j * v i * v j)
        = ((n : ℝ) - 1) * (∑ i, ∑ j, id2 n i j * v i * v j) := by
      have hp : ∀ i j : Fin n, ric (Iso n) i j * v i * v j
          = ((n : ℝ) - 1) * (id2 n i j * v i * v j) := by
        intro i j; rw [ric_iso n i j]; ring
      rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hp i j)),
        Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]
    have h3 : (∑ i, ∑ j, id2 n i j * v i * v j) = ∑ i, v i * v i := qform_id2_eq v
    rw [h2, h3]
  rw [h1, scalAlg_iso]
  have hkey : (n : ℝ) * ((n : ℝ) - 1) / (n : ℝ) = (n : ℝ) - 1 :=
    mul_div_cancel_left₀ _ hne
  rw [mul_div_assoc, hkey]
  ring

/-! ## 2. Elementary norm bounds -/

lemma norm_le_of_components₂ {A : Fin n → Fin n → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, |A i j| ≤ c) : ‖A‖ ≤ c := by
  rw [pi_norm_le_iff_of_nonneg hc]
  intro i
  rw [pi_norm_le_iff_of_nonneg hc]
  intro j
  simpa using h i j

lemma norm_Iso_le_one (n : ℕ) : ‖Iso n‖ ≤ 1 := by
  refine norm_le_of_components (by norm_num) (fun i j k l => ?_)
  have h : Iso n i j k l = 1 ∨ Iso n i j k l = 0 ∨ Iso n i j k l = -1 := by
    simp only [Iso]
    split_ifs <;> norm_num
  rcases h with h | h | h <;> rw [h] <;> norm_num

lemma norm_id2_le_one (n : ℕ) : ‖id2 n‖ ≤ 1 := by
  refine norm_le_of_components₂ (by norm_num) (fun i j => ?_)
  simp only [id2]
  split_ifs <;> norm_num

lemma norm_knProd_le (A B : Fin n → Fin n → ℝ) : ‖knProd A B‖ ≤ 4 * ‖A‖ * ‖B‖ := by
  have hA : ∀ p q : Fin n, |A p q| ≤ ‖A‖ := fun p q =>
    calc |A p q| = ‖A p q‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖A p‖ := norm_le_pi_norm (A p) q
      _ ≤ ‖A‖ := norm_le_pi_norm A p
  have hB : ∀ p q : Fin n, |B p q| ≤ ‖B‖ := fun p q =>
    calc |B p q| = ‖B p q‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖B p‖ := norm_le_pi_norm (B p) q
      _ ≤ ‖B‖ := norm_le_pi_norm B p
  have hAnn : 0 ≤ ‖A‖ := norm_nonneg A
  refine norm_le_of_components (by positivity) (fun i j k l => ?_)
  simp only [knProd]
  have h2 : |A i k * B j l - A i l * B j k| ≤ ‖A‖ * ‖B‖ + ‖A‖ * ‖B‖ := by
    calc |A i k * B j l - A i l * B j k| ≤ |A i k * B j l| + |A i l * B j k| := abs_sub _ _
      _ = |A i k| * |B j l| + |A i l| * |B j k| := by rw [abs_mul, abs_mul]
      _ ≤ ‖A‖ * ‖B‖ + ‖A‖ * ‖B‖ :=
          add_le_add (mul_le_mul (hA i k) (hB j l) (abs_nonneg _) hAnn)
            (mul_le_mul (hA i l) (hB j k) (abs_nonneg _) hAnn)
  have h3 : |A j k * B i l| ≤ ‖A‖ * ‖B‖ := by
    rw [abs_mul]; exact mul_le_mul (hA j k) (hB i l) (abs_nonneg _) hAnn
  have h4 : |A j l * B i k| ≤ ‖A‖ * ‖B‖ := by
    rw [abs_mul]; exact mul_le_mul (hA j l) (hB i k) (abs_nonneg _) hAnn
  have h5 : |A i k * B j l - A i l * B j k - A j k * B i l| ≤
      (‖A‖ * ‖B‖ + ‖A‖ * ‖B‖) + ‖A‖ * ‖B‖ := by
    calc |A i k * B j l - A i l * B j k - A j k * B i l|
        ≤ |A i k * B j l - A i l * B j k| + |A j k * B i l| := abs_sub _ _
      _ ≤ (‖A‖ * ‖B‖ + ‖A‖ * ‖B‖) + ‖A‖ * ‖B‖ := by linarith
  have h6 : |A i k * B j l - A i l * B j k - A j k * B i l + A j l * B i k| ≤
      ((‖A‖ * ‖B‖ + ‖A‖ * ‖B‖) + ‖A‖ * ‖B‖) + ‖A‖ * ‖B‖ := by
    have h := abs_sub (A i k * B j l - A i l * B j k - A j k * B i l) (-(A j l * B i k))
    rw [sub_neg_eq_add, abs_neg] at h
    linarith
  linarith

lemma norm_knProd_id2_le (A : Fin n → Fin n → ℝ) : ‖knProd A (id2 n)‖ ≤ 4 * ‖A‖ := by
  have h := norm_knProd_le A (id2 n)
  have h2 := norm_id2_le_one n
  have hA : 0 ≤ ‖A‖ := norm_nonneg A
  calc ‖knProd A (id2 n)‖ ≤ 4 * ‖A‖ * ‖id2 n‖ := h
    _ ≤ 4 * ‖A‖ * 1 := by nlinarith
    _ = 4 * ‖A‖ := by ring

lemma norm_ric_le (hn : 2 ≤ n) (T : Curv4 n) : ‖ric T‖ ≤ (n : ℝ) * ‖T‖ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  refine norm_le_of_components₂ (by positivity) (fun i j => ?_)
  simpa using chat_linv_abs_ric T i j

lemma norm_ric0_le (hn : 2 ≤ n) (T : Curv4 n) : ‖ric0 T‖ ≤ 2 * (n : ℝ) * ‖T‖ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  refine norm_le_of_components₂ (by positivity) (fun i j => ?_)
  have h2 : ric0 T i j = ric T i j - scalAlg T / (n : ℝ) * id2 n i j := rfl
  have h1 : |ric0 T i j| ≤ |ric T i j| + |scalAlg T / (n : ℝ)| * |id2 n i j| := by
    rw [h2]
    calc |ric T i j - scalAlg T / (n : ℝ) * id2 n i j|
        ≤ |ric T i j| + |scalAlg T / (n : ℝ) * id2 n i j| := abs_sub _ _
      _ = |ric T i j| + |scalAlg T / (n : ℝ)| * |id2 n i j| := by rw [abs_mul]
  have h3 : |ric T i j| ≤ (n : ℝ) * ‖T‖ := chat_linv_abs_ric T i j
  have h4 : |scalAlg T / (n : ℝ)| ≤ (n : ℝ) * ‖T‖ := by
    have h5 : |scalAlg T / (n : ℝ)| = |scalAlg T| / (n : ℝ) := by
      rw [abs_div]
      exact congrArg (fun x => |scalAlg T| / x) (abs_of_nonneg (Nat.cast_nonneg n))
    rw [h5, div_le_iff₀ hn0]
    calc |scalAlg T| ≤ (n : ℝ) ^ 2 * ‖T‖ := chat_linv_abs_scalAlg T
      _ = (n : ℝ) * ‖T‖ * (n : ℝ) := by ring
  have h6 : |id2 n i j| ≤ 1 := by
    simp only [id2]; split_ifs <;> norm_num
  have h7 : |scalAlg T / (n : ℝ)| * |id2 n i j| ≤ (n : ℝ) * ‖T‖ := by
    calc |scalAlg T / (n : ℝ)| * |id2 n i j| ≤ ((n : ℝ) * ‖T‖) * 1 :=
          mul_le_mul h4 h6 (abs_nonneg _) (by positivity)
      _ = (n : ℝ) * ‖T‖ := by ring
  linarith

lemma norm_knProd_id2_id2_le (n : ℕ) : ‖knProd (id2 n) (id2 n)‖ ≤ 2 := by
  rw [knProd_id2_id2_eq_two_smul]
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have h := norm_Iso_le_one n
  linarith

/-- `linv a b` is bounded on the admissible parameter range, uniformly in the tensor. -/
lemma norm_linv_le (hn : 2 ≤ n) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hb' : b ≤ 1 / 2)
    (T : Curv4 n) : ‖linv a b T‖ ≤ (10 * (n : ℝ) + 1) * ‖T‖ := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hT : 0 ≤ ‖T‖ := norm_nonneg T
  have hb1 : 0 < 1 + ((n : ℝ) - 2) * b := by nlinarith
  have ha1 : 0 < 1 + 2 * ((n : ℝ) - 1) * a := by nlinarith
  have hcoef1 : |b / (1 + ((n : ℝ) - 2) * b)| ≤ 1 := by
    have e1 : |b / (1 + ((n : ℝ) - 2) * b)| = |b| / |1 + ((n : ℝ) - 2) * b| := abs_div _ _
    have e2 : |1 + ((n : ℝ) - 2) * b| = 1 + ((n : ℝ) - 2) * b := abs_of_pos hb1
    have e3 : |b| = b := abs_of_nonneg hb
    rw [e1, e2, e3, div_le_one hb1]
    have h3 : ((n : ℝ) - 3) * b ≥ -1 * b :=
      mul_le_mul_of_nonneg_right (by linarith : (-1 : ℝ) ≤ (n : ℝ) - 3) hb
    linarith
  have hcoef2 : a / (n : ℝ) / (1 + 2 * ((n : ℝ) - 1) * a) ≤ 1 / (2 * ((n : ℝ) - 1)) := by
    have hden0 : (0 : ℝ) < 1 + 2 * ((n : ℝ) - 1) * a := by linarith
    have hden : (0 : ℝ) < n * (1 + 2 * ((n : ℝ) - 1) * a) := mul_pos hn0 hden0
    have hden2 : (0 : ℝ) < 2 * ((n : ℝ) - 1) := by linarith
    rw [div_div, div_le_iff₀ hden]
    rw [div_mul_eq_mul_div, le_div_iff₀ hden2]
    nlinarith [ha, hn2, mul_nonneg ha (le_of_lt hden2)]
  have hc2 : |(a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg T| ≤ (n : ℝ) * ‖T‖ := by
    have hden0 : (0 : ℝ) < 1 + 2 * ((n : ℝ) - 1) * a := by linarith
    have hnn : (0 : ℝ) ≤ a / (n : ℝ) / (1 + 2 * ((n : ℝ) - 1) * a) :=
      div_nonneg (div_nonneg ha (le_of_lt hn0)) (le_of_lt hden0)
    rw [abs_mul, abs_of_nonneg hnn]
    have hstep : a / (n : ℝ) / (1 + 2 * ((n : ℝ) - 1) * a) * |scalAlg T|
        ≤ (1 / (2 * ((n : ℝ) - 1))) * ((n : ℝ) ^ 2 * ‖T‖) :=
      mul_le_mul hcoef2 (chat_linv_abs_scalAlg T) (abs_nonneg _)
        (div_nonneg zero_le_one (by linarith : (0 : ℝ) ≤ 2 * ((n : ℝ) - 1)))
    have hstep2 : (1 / (2 * ((n : ℝ) - 1))) * ((n : ℝ) ^ 2 * ‖T‖) ≤ (n : ℝ) * ‖T‖ := by
      have h3 : (1 / (2 * ((n : ℝ) - 1))) * ((n : ℝ) ^ 2 * ‖T‖)
          = ((n : ℝ) * ‖T‖) * ((n : ℝ) / (2 * ((n : ℝ) - 1))) := by ring
      rw [h3]
      have h4 : (n : ℝ) / (2 * ((n : ℝ) - 1)) ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      calc ((n : ℝ) * ‖T‖) * ((n : ℝ) / (2 * ((n : ℝ) - 1)))
          ≤ ((n : ℝ) * ‖T‖) * 1 := mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = (n : ℝ) * ‖T‖ := by ring
    linarith
  have hsplit : linv a b T = T - (b / (1 + ((n : ℝ) - 2) * b)) • knProd (ric0 T) (id2 n)
      - ((a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg T) • knProd (id2 n) (id2 n) := by
    rw [linv]
  rw [hsplit]
  have h1 : ‖T - (b / (1 + ((n : ℝ) - 2) * b)) • knProd (ric0 T) (id2 n)
      - ((a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg T) • knProd (id2 n) (id2 n)‖
      ≤ ‖T - (b / (1 + ((n : ℝ) - 2) * b)) • knProd (ric0 T) (id2 n)‖
        + ‖((a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg T) • knProd (id2 n) (id2 n)‖ :=
    norm_sub_le _ _
  have h2 : ‖T - (b / (1 + ((n : ℝ) - 2) * b)) • knProd (ric0 T) (id2 n)‖
      ≤ ‖T‖ + ‖(b / (1 + ((n : ℝ) - 2) * b)) • knProd (ric0 T) (id2 n)‖ := norm_sub_le _ _
  have h3 : ‖(b / (1 + ((n : ℝ) - 2) * b)) • knProd (ric0 T) (id2 n)‖ ≤ 4 * ‖ric0 T‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |b / (1 + ((n : ℝ) - 2) * b)| * ‖knProd (ric0 T) (id2 n)‖
        ≤ 1 * (4 * ‖ric0 T‖) := mul_le_mul hcoef1 (norm_knProd_id2_le (ric0 T))
          (norm_nonneg _) (by norm_num)
      _ = 4 * ‖ric0 T‖ := by ring
  have h4 : ‖((a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg T) • knProd (id2 n) (id2 n)‖
      ≤ (n : ℝ) * ‖T‖ * 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |(a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg T| * ‖knProd (id2 n) (id2 n)‖
        ≤ ((n : ℝ) * ‖T‖) * 2 :=
          mul_le_mul hc2 (norm_knProd_id2_id2_le n) (norm_nonneg _) (by positivity)
      _ = (n : ℝ) * ‖T‖ * 2 := by ring
  have h5 : ‖ric0 T‖ ≤ 2 * (n : ℝ) * ‖T‖ := norm_ric0_le hn T
  linarith

/-! ## 3. Bounds on the shifted reaction direction -/

/-- `K_E` dominates `‖linv a b (knProd (ric0 S) (id2 n))‖ / ((1-p)σ)`. -/
noncomputable def cssKE (n : ℕ) : ℝ :=
  (10 * (n : ℝ) + 1) * 4 * Real.sqrt ((n : ℝ) * ((n : ℝ) - 1)) / (n : ℝ)

/-- `K_P` dominates the perturbation coefficient of the Ricci form. -/
noncomputable def cssKP (n : ℕ) : ℝ :=
  2 * ((n : ℝ) - 1) / (n : ℝ) + (1 + ((n : ℝ) - 2) / 2) * (2 * (n : ℝ) ^ 2) * cssKE n

/-- `K_P^E` dominates the perturbation coefficient of the isotropic-curvature form. -/
noncomputable def cssKPE (n : ℕ) (KEF : ℝ) : ℝ :=
  2 / (n : ℝ) + (1 + ((n : ℝ) - 2) / 2) * KEF * cssKE n

/-! ## 4. The shifted reaction direction -/

/-- The cast bridge `↑(2(n-1)) = 2(↑n - 1)`. -/
lemma two_nat_sub_one_cast (n : ℕ) (hn : 1 ≤ n) :
    ((2 * (n - 1) : ℕ) : ℝ) = 2 * ((n : ℝ) - 1) := by
  rw [Nat.cast_mul, Nat.cast_sub hn, Nat.cast_one, Nat.cast_ofNat]

/-- `Q` on a shift of the round sphere. -/
lemma Q_shift_expand (n : ℕ) (Y : Curv4 n) (hY : IsAlgCurv Y) (c : ℝ) :
    Q (Y - c • Iso n) = Q Y + (c ^ 2 * ((2 * (n - 1) : ℕ) : ℝ)) • Iso n
      - (2 * c) • BQ Y (Iso n) := by
  have hsub : Y - c • Iso n = Y + (-c) • Iso n := by
    ext i j k l
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsub, Q_add_polarize, Work.Diff.PP.Q_smul, BQ_smul_right, Q_iso]
  ext i j k l
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- **The shifted reaction direction.**  `chatLinv n s (Q (Y - ĉ • Iso n))` is the unshifted
`linv a b (Q Y)` plus a multiple of `Iso n` (the `ĉ²` term) minus `2 ĉ` times the linearization
`linv a b (knProd (ric Y) (id2 n))`. -/
lemma chatLinv_shift_expand (n : ℕ) (hn : 2 ≤ n) {s ĉ : ℝ} (hs : 0 < s) {Y : Curv4 n}
    (hY : IsAlgCurv Y) :
    chatLinv n s (Q (Y - ĉ • Iso n))
      = linv (chatAA n s) (chatBB s) (Q Y)
        + (ĉ ^ 2 * (((2 * (n - 1) : ℕ) : ℝ) * (1 / (1 + 2 * ((n : ℝ) - 1) * chatAA n s)))) • Iso n
        - (2 * ĉ) • linv (chatAA n s) (chatBB s) (knProd (ric Y) (id2 n)) := by
  have hn1 : 1 ≤ n := by omega
  have ha : 0 ≤ chatAA n s := chatAA_nonneg n hn hs.le
  have hden : 1 + 2 * ((n : ℝ) - 1) * chatAA n s ≠ 0 := by
    have h1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have : (0 : ℝ) < 1 + 2 * ((n : ℝ) - 1) * chatAA n s := by nlinarith [ha, h1]
    exact ne_of_gt this
  rw [chatLinv_eq_linv n hn hs.le, Q_shift_expand n Y hY ĉ, BQ_iso n hY]
  simp only [linv_sub, linv_add, linv_smul, cm_linv_iso (n := n) hn1 hden, smul_smul]
  ext i j k l
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The Ricci tensor of the preimage: for `Y = ell a b S` with `scalAlg Y = 1`, the Ricci tensor
of `Y` is `(1+(n-2)b) • Ric₀ S + (1/n) • id`. -/
lemma ric_of_preimage {a b : ℝ} {S Y : Curv4 n} (hYalg : IsAlgCurv S)
    (hY : Y = ell a b S) (hscal : scalAlg Y = 1) :
    ric Y = (1 + ((n : ℝ) - 2) * b) • ric0 S + (1 / (n : ℝ)) • id2 n := by
  have hS := hYalg
  have hn0 : ((n : ℝ)) ≠ 0 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      exfalso
      simp [scalAlg] at hscal
    · exact_mod_cast (Nat.pos_iff_ne_zero.mp h)
  funext i j
  rw [hY, ric_ell_aux a b hn0 hS i j]
  have hone : (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg S = 1 := by
    have h2 := scalAlg_ell (n := n) a b S
    rw [← hY, hscal] at h2
    exact h2.symm
  have hcoef : scalAlg S * (1 + 2 * ((n : ℝ) - 1) * a) / (n : ℝ) = 1 / (n : ℝ) := by
    rw [mul_comm, hone]
  rw [hcoef]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, id2]

/-- The linearization tensor `M` of the shift: `knProd (ric Y) (id2 n)` splits off the
round-sphere part. -/
lemma knProd_ric_decomp {a b : ℝ} {S Y : Curv4 n} (hYalg : IsAlgCurv S)
    (hY : Y = ell a b S) (hscal : scalAlg Y = 1) :
    knProd (ric Y) (id2 n)
      = (1 + ((n : ℝ) - 2) * b) • knProd (ric0 S) (id2 n) + (2 / (n : ℝ)) • Iso n := by
  have hric : ric Y = (1 + ((n : ℝ) - 2) * b) • ric0 S + (1 / (n : ℝ)) • id2 n :=
    ric_of_preimage hYalg hY hscal
  rw [hric, knProd_add_left, knProd_smul_left, knProd_smul_left, knProd_id2_id2_eq_two_smul]
  simp only [smul_smul]
  rw [show (1 / (n : ℝ)) * 2 = 2 / (n : ℝ) from by ring]

/-- The `linv`-image of the linearization tensor. -/
lemma linv_knProd_ric_decomp {a b : ℝ} {S Y : Curv4 n} (hn : 2 ≤ n)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hYalg : IsAlgCurv S)
    (hY : Y = ell a b S) (hscal : scalAlg Y = 1) :
    linv a b (knProd (ric Y) (id2 n))
      = (1 + ((n : ℝ) - 2) * b) • linv a b (knProd (ric0 S) (id2 n))
        + (2 / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * a))) • Iso n := by
  have hn1 : 1 ≤ n := by omega
  have hden : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0 := by
    have h1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have : (0 : ℝ) < 1 + 2 * ((n : ℝ) - 1) * a := by nlinarith [ha, h1]
    exact ne_of_gt this
  rw [knProd_ric_decomp hYalg hY hscal, linv_add, linv_smul, linv_smul,
    cm_linv_iso (n := n) hn1 hden]
  rw [show (2 / (n : ℝ)) • ((1 / (1 + 2 * ((n : ℝ) - 1) * a)) • Iso n)
      = (2 / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * a))) • Iso n from by
    rw [smul_smul]
    congr 1
    field_simp]

/-- The bound `‖linv a b (knProd (ric0 S) (id2 n))‖ ≤ K_E (1-p)σ`. -/
lemma norm_linv_knProd_ric0_le (n : ℕ) (hn : 2 ≤ n) {p σ : ℝ} (hp : p ≤ 1) (hσ : 0 < σ)
    {S : Curv4 n} (hS : IsAlgCurv S) (hric : RicPinch p S) (hsc : scalAlg S = σ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hb' : b ≤ 1 / 2) :
    ‖linv a b (knProd (ric0 S) (id2 n))‖ ≤ cssKE n * (1 - p) * σ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hfrob : ric0Frob2 S
      ≤ (n : ℝ) * ((n : ℝ) - 1) * (1 - p) ^ 2 * (scalAlg S / (n : ℝ)) ^ 2 :=
    ric0Frob2_le n hp hS hric (by rw [hsc]; exact div_pos hσ hn0)
  have hric0 : ‖ric0 S‖ ≤ Real.sqrt ((n : ℝ) * ((n : ℝ) - 1)) * (1 - p) * (σ / (n : ℝ)) := by
    refine norm_le_of_components₂ (by positivity) (fun i j => ?_)
    have h3 : (ric0 S i j) ^ 2 ≤ ric0Frob2 S := by
      rw [ric0Frob2]
      calc (ric0 S i j) ^ 2 = ric0 S i j * ric0 S i j := by ring
        _ ≤ ∑ j', ric0 S i j' * ric0 S i j' :=
            Finset.single_le_sum (fun j' _ => mul_self_nonneg (ric0 S i j')) (Finset.mem_univ j)
        _ ≤ ∑ i', ∑ j', ric0 S i' j' * ric0 S i' j' :=
            Finset.single_le_sum (fun i' _ => Finset.sum_nonneg (fun j' _ => mul_self_nonneg _))
              (Finset.mem_univ i)
    have h4 : |ric0 S i j| ≤ Real.sqrt (ric0Frob2 S) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt h3
    have h5 : Real.sqrt (ric0Frob2 S)
        ≤ Real.sqrt ((n : ℝ) * ((n : ℝ) - 1) * (1 - p) ^ 2 * (scalAlg S / (n : ℝ)) ^ 2) :=
      Real.sqrt_le_sqrt hfrob
    have h6 : Real.sqrt ((n : ℝ) * ((n : ℝ) - 1) * (1 - p) ^ 2 * (scalAlg S / (n : ℝ)) ^ 2)
        = Real.sqrt ((n : ℝ) * ((n : ℝ) - 1)) * (1 - p) * (σ / (n : ℝ)) := by
      have hsq : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
        have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        nlinarith
      have hsq2 : (0 : ℝ) ≤ (1 - p) * (scalAlg S / (n : ℝ)) := by
        have hp1 : (0 : ℝ) ≤ 1 - p := by linarith
        exact mul_nonneg hp1 (div_nonneg (by rw [hsc]; exact le_of_lt hσ) hn0.le)
      rw [show (n : ℝ) * ((n : ℝ) - 1) * (1 - p) ^ 2 * (scalAlg S / (n : ℝ)) ^ 2
          = ((n : ℝ) * ((n : ℝ) - 1)) * ((1 - p) * (scalAlg S / (n : ℝ))) ^ 2 from by ring,
        Real.sqrt_mul hsq, Real.sqrt_sq hsq2, hsc]
      ring
    linarith [h4, h5, h6.le, h6.ge]
  have hT : ‖knProd (ric0 S) (id2 n)‖
      ≤ 4 * Real.sqrt ((n : ℝ) * ((n : ℝ) - 1)) * (1 - p) * (σ / (n : ℝ)) := by
    calc ‖knProd (ric0 S) (id2 n)‖ ≤ 4 * ‖ric0 S‖ := norm_knProd_id2_le _
      _ ≤ 4 * (Real.sqrt ((n : ℝ) * ((n : ℝ) - 1)) * (1 - p) * (σ / (n : ℝ))) := by linarith
      _ = 4 * Real.sqrt ((n : ℝ) * ((n : ℝ) - 1)) * (1 - p) * (σ / (n : ℝ)) := by ring
  have hlinv := norm_linv_le hn a b ha hb hb' (knProd (ric0 S) (id2 n))
  have hke : cssKE n = (10 * (n : ℝ) + 1) * 4 * Real.sqrt ((n : ℝ) * ((n : ℝ) - 1)) / (n : ℝ) := rfl
  calc ‖linv a b (knProd (ric0 S) (id2 n))‖
      ≤ (10 * (n : ℝ) + 1) * ‖knProd (ric0 S) (id2 n)‖ := hlinv
    _ ≤ (10 * (n : ℝ) + 1)
          * (4 * Real.sqrt ((n : ℝ) * ((n : ℝ) - 1)) * (1 - p) * (σ / (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ = cssKE n * (1 - p) * σ := by rw [hke]; field_simp

/-- **The traceless Ricci tensor of a tight direction.**  If `v ≠ 0` saturates the Ricci
pinching of `S`, then `(1-p)² (scal S/n)² ≤ |Ric₀ S|²`: the tight direction is an eigenvector of
`Ric₀` with eigenvalue `(p-1)·scal S/n`. -/
lemma ric0Frob2_tight_lower (n : ℕ) {p : ℝ} (hp : p < 1) {S : Curv4 n}
    (hS : IsAlgCurv S) (hric : RicPinch p S) {v : Fin n → ℝ} (hv : v ≠ 0)
    (htight : (p * scalAlg S / (n : ℝ)) * (∑ i, v i * v i)
      = ∑ i, ∑ j, ric S i j * v i * v j) :
    (1 - p) ^ 2 * (scalAlg S / (n : ℝ)) ^ 2 ≤ ric0Frob2 S := by
  have hq : 0 < ∑ i, v i * v i := by
    obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv (funext fun i => h i)
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ v i * v i :=
      fun i _ => mul_self_nonneg (v i)
    have hle : v i₀ * v i₀ ≤ ∑ i, v i * v i :=
      Finset.single_le_sum hnn (Finset.mem_univ i₀)
    have hlt : 0 < v i₀ * v i₀ := mul_self_pos.mpr hi₀
    linarith
  have hev : ∀ i, ∑ j, ric0 S i j * v j = (p - 1) * (scalAlg S / (n : ℝ)) * v i :=
    fun i => ric0_mulVec_of_tight n hp hS hric htight i
  have hcs : ∀ i, (∑ j, ric0 S i j * v j) ^ 2 ≤ (∑ j, ric0 S i j ^ 2) * (∑ j, v j * v j) := by
    intro i
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ric0 S i j) v
    simpa only [pow_two] using h
  have h1 : (1 - p) ^ 2 * (scalAlg S / (n : ℝ)) ^ 2 * (∑ i, v i * v i)
      = ∑ i, (∑ j, ric0 S i j * v j) ^ 2 := by
    have h7 : ∀ i : Fin n,
        (∑ j, ric0 S i j * v j) ^ 2 = ((p - 1) * (scalAlg S / (n : ℝ)) * v i) ^ 2 := fun i => by
      rw [hev i]
    rw [Finset.sum_congr rfl (fun i _ => h7 i)]
    rw [show (∑ i, ((p - 1) * (scalAlg S / (n : ℝ)) * v i) ^ 2)
        = ((p - 1) * (scalAlg S / (n : ℝ))) ^ 2 * (∑ i, v i * v i) from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)]
    ring
  have h2 : (∑ i, (∑ j, ric0 S i j * v j) ^ 2) ≤ ric0Frob2 S * (∑ i, v i * v i) := by
    calc (∑ i, (∑ j, ric0 S i j * v j) ^ 2)
        ≤ ∑ i, (∑ j, ric0 S i j ^ 2) * (∑ j, v j * v j) :=
          Finset.sum_le_sum (fun i _ => hcs i)
      _ = (∑ i, ∑ j, ric0 S i j ^ 2) * (∑ j, v j * v j) := by rw [Finset.sum_mul]
      _ = ric0Frob2 S * (∑ j, v j * v j) := by
          rw [ric0Frob2]
          congr 1
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [pow_two]
  rw [← h1] at h2
  exact le_of_mul_le_mul_right h2 hq


/-! ## 4. The quantitative pointwise margins -/

/-- **Quantitative Böhm–Wilking strictness, branch `0 < b ≤ 1/2`**: at a tight direction the
pulled-back reaction direction improves the Ricci form by at least
`4 · ccA n b · ccP n b · (scal S/n)² · EFun (Iso n)` on every degenerate direction. -/
theorem efun_margin_b (n : ℕ) (hn2 : 2 ≤ n) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2)
    {S : Submission.Diff.Alg.Curv4 n} (hS : Submission.Diff.Alg.IsAlgCurv S)
    (hS0 : S ≠ 0)
    (hP : Submission.Diff.Alg.InPIC2 S)
    (hric : Work.Diff.Alg.Pinch.RicPinch (Work.Diff.Alg.Pinch.ccP n b) S)
    (x y z w : Fin n → ℝ) (hdeg : Work.Diff.Alg.Q2P.EFun S x y z w = 0)
    (hIso : Work.Diff.Alg.Q2P.EFun (Submission.Diff.Alg.Iso n) x y z w ≠ 0) :
    4 * Work.Diff.Alg.Pinch.ccA n b * Work.Diff.Alg.Pinch.ccP n b
        * (Submission.Diff.Alg.scalAlg S / ↑n) ^ 2
        * Work.Diff.Alg.Q2P.EFun (Submission.Diff.Alg.Iso n) x y z w
      ≤ Work.Diff.Alg.Q2P.EFun
          (Work.Diff.Alg.Pinch.linv (Work.Diff.Alg.Pinch.ccA n b) b
            (Submission.Diff.Alg.Q (Work.Diff.Alg.Pinch.ell (Work.Diff.Alg.Pinch.ccA n b) b S)))
          x y z w := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hX : linv (ccA n b) b (Q (ell (ccA n b) b S)) = Q S + Dtensor n b S :=
    chat_linv_Q_ell_eq n hn1 hn0 hb hb' hS
  have hdt : Dtensor n b S = bwCorr (ccA n b) b S := rfl
  rw [hX, Q2P_EFun_add, hdt]
  have h1 : 0 ≤ Q2P.EFun (Q S) x y z w := inPIC2_Q_pointwise n S hS hP x y z w hdeg
  have h2 := chatb_bwCorr_bound n hn2 hb hb' hS hric x y z w
  linarith

/-- **Quantitative Böhm–Wilking strictness, branch `1/2 < a`** for the isotropic-curvature form. -/
theorem efun_margin_a (n : ℕ) (hn3 : 3 ≤ n) {a : ℝ} (ha : 1 / 2 < a)
    {S : Submission.Diff.Alg.Curv4 n} (hS : Submission.Diff.Alg.IsAlgCurv S)
    (hS0 : S ≠ 0)
    (hP : Submission.Diff.Alg.InPIC2 S)
    (hric : Work.Diff.Alg.Pinch.RicPinch (1 - 4 / ((n : ℝ) - 2 + 8 * a)) S)
    (x y z w : Fin n → ℝ) (hdeg : Work.Diff.Alg.Q2P.EFun S x y z w = 0)
    (hIso : Work.Diff.Alg.Q2P.EFun (Submission.Diff.Alg.Iso n) x y z w ≠ 0) :
    2 * Work.Diff.Alg.Pinch.efaPsi n a * (Submission.Diff.Alg.scalAlg S / ↑n) ^ 2
        * Work.Diff.Alg.Q2P.EFun (Submission.Diff.Alg.Iso n) x y z w
      ≤ Work.Diff.Alg.Q2P.EFun
          (Work.Diff.Alg.Pinch.linv a (1 / 2)
            (Submission.Diff.Alg.Q (Work.Diff.Alg.Pinch.ell a (1 / 2) S))) x y z w := by
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hn0R : (0 : ℝ) < (n : ℝ) := by linarith
  have hs : 0 < bwS a := by rw [bwS]; linarith
  have hlam : 0 < bwLam n S :=
    scalAlg_pos_of_inPIC2_ricpinch n hn2 ha hS hS0 hP hric
  have hlam' : bwLam n S = scalAlg S / (n : ℝ) := rfl
  have hDden : (0 : ℝ) < (n : ℝ) + 2 + 4 * bwS a := by linarith
  have hDdenne : ((n : ℝ) + 2 + 4 * bwS a) ^ 2 ≠ 0 := by positivity
  have hD2pos : (0 : ℝ) < ((n : ℝ) + 2 + 4 * bwS a) ^ 2 := by positivity
  have hEden : (0 : ℝ) < (n : ℝ) + ((n : ℝ) - 1) * bwS a := by nlinarith
  have hEge : (n : ℝ) ≤ (n : ℝ) + ((n : ℝ) - 1) * bwS a := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - 1) (le_of_lt hs)]
  -- the Frobenius bound
  have hFrob : ric0Frob2 S * ((n : ℝ) + 2 + 4 * bwS a) ^ 2
      ≤ 16 * (n : ℝ) * ((n : ℝ) - 1) * (bwLam n S) ^ 2 := by
    have hp : 1 - 4 / ((n : ℝ) - 2 + 8 * a) ≤ 1 := by
      have hpos : (0 : ℝ) < 4 / ((n : ℝ) - 2 + 8 * a) := by
        apply div_pos (by norm_num); linarith
      linarith
    have h := ric0Frob2_le n (p := 1 - 4 / ((n : ℝ) - 2 + 8 * a)) hp hS hric
      (by simpa only [bwLam] using hlam)
    have h1 : (n : ℝ) - 2 + 8 * a = (n : ℝ) + 2 + 4 * bwS a := by rw [bwS]; ring
    rw [h1] at h
    have h2 : (1 - (1 - 4 / ((n : ℝ) + 2 + 4 * bwS a))) = 4 / ((n : ℝ) + 2 + 4 * bwS a) := by ring
    rw [h2] at h
    have h4 : (4 / ((n : ℝ) + 2 + 4 * bwS a)) ^ 2 * ((n : ℝ) + 2 + 4 * bwS a) ^ 2 = 16 := by
      rw [div_pow]
      rw [show (4 ^ 2 / ((n : ℝ) + 2 + 4 * bwS a) ^ 2) * ((n : ℝ) + 2 + 4 * bwS a) ^ 2
          = 4 ^ 2 * ((((n : ℝ) + 2 + 4 * bwS a) ^ 2)⁻¹
              * ((n : ℝ) + 2 + 4 * bwS a) ^ 2) from by
        rw [div_eq_mul_inv]; ring]
      rw [inv_mul_cancel₀ hDdenne, mul_one]
      norm_num
    calc ric0Frob2 S * ((n : ℝ) + 2 + 4 * bwS a) ^ 2
        ≤ ((n : ℝ) * ((n : ℝ) - 1) * (4 / ((n : ℝ) + 2 + 4 * bwS a)) ^ 2
            * (bwLam n S) ^ 2) * ((n : ℝ) + 2 + 4 * bwS a) ^ 2 :=
          mul_le_mul_of_nonneg_right h (le_of_lt hD2pos)
      _ = (n : ℝ) * ((n : ℝ) - 1)
            * ((4 / ((n : ℝ) + 2 + 4 * bwS a)) ^ 2 * ((n : ℝ) + 2 + 4 * bwS a) ^ 2)
            * (bwLam n S) ^ 2 := by ring
      _ = 16 * (n : ℝ) * ((n : ℝ) - 1) * (bwLam n S) ^ 2 := by rw [h4]; ring
  -- the coefficient bound
  have hG : bwLam n S ^ 2 * efaPsi n a ≤ bwGamma n a S := by
    have hep : efaPsi n a = ((n : ℝ) - 2) / ((n : ℝ) + 2)
        + bwS a * (((n : ℝ) - 6 + 4 * bwS a) / ((n : ℝ) + 2 + 4 * bwS a))
        - 4 * bwS a * ((n : ℝ) - 1) / ((n : ℝ) + 2 + 4 * bwS a) ^ 2 := by
      simp only [efaPsi, bwS]
    rw [bwGamma_eq, hep]
    have hcoe : (0 : ℝ) ≤ 16 * bwS a * ((n : ℝ) - 1) * (bwLam n S) ^ 2 := by positivity
    have hkey : bwS a * ric0Frob2 S * ((n : ℝ) + 2 + 4 * bwS a) ^ 2
        ≤ 16 * bwS a * ((n : ℝ) - 1) * (bwLam n S) ^ 2
          * ((n : ℝ) + ((n : ℝ) - 1) * bwS a) := by
      have h1 : bwS a * (ric0Frob2 S * ((n : ℝ) + 2 + 4 * bwS a) ^ 2)
          ≤ bwS a * (16 * (n : ℝ) * ((n : ℝ) - 1) * (bwLam n S) ^ 2) :=
        mul_le_mul_of_nonneg_left hFrob (le_of_lt hs)
      have h2 : 16 * bwS a * (n : ℝ) * ((n : ℝ) - 1) * (bwLam n S) ^ 2
          ≤ 16 * bwS a * ((n : ℝ) - 1) * (bwLam n S) ^ 2
            * ((n : ℝ) + ((n : ℝ) - 1) * bwS a) := by
        have h3 := mul_le_mul_of_nonneg_left hEge hcoe
        nlinarith [h3]
      nlinarith [h1, h2]
    have hb : bwS a * ric0Frob2 S / (4 * ((n : ℝ) + ((n : ℝ) - 1) * bwS a))
        ≤ (bwLam n S) ^ 2 * (4 * bwS a * ((n : ℝ) - 1) / ((n : ℝ) + 2 + 4 * bwS a) ^ 2) := by
      have h4E : (0 : ℝ) < 4 * ((n : ℝ) + ((n : ℝ) - 1) * bwS a) := by positivity
      rw [div_le_iff₀ h4E]
      have hgoal : (bwLam n S) ^ 2
            * (4 * bwS a * ((n : ℝ) - 1) / ((n : ℝ) + 2 + 4 * bwS a) ^ 2)
            * (4 * ((n : ℝ) + ((n : ℝ) - 1) * bwS a))
          = (bwLam n S) ^ 2 * (4 * bwS a * ((n : ℝ) - 1))
            * (4 * ((n : ℝ) + ((n : ℝ) - 1) * bwS a))
            / ((n : ℝ) + 2 + 4 * bwS a) ^ 2 := by
        rw [div_eq_mul_inv]
        ring
      rw [hgoal, le_div_iff₀ hD2pos]
      nlinarith [hkey]
    have hdist : bwLam n S ^ 2 * (((n : ℝ) - 2) / ((n : ℝ) + 2)
          + bwS a * (((n : ℝ) - 6 + 4 * bwS a) / ((n : ℝ) + 2 + 4 * bwS a))
          - 4 * bwS a * ((n : ℝ) - 1) / ((n : ℝ) + 2 + 4 * bwS a) ^ 2)
        = bwLam n S ^ 2 * (((n : ℝ) - 2) / ((n : ℝ) + 2)
            + bwS a * (((n : ℝ) - 6 + 4 * bwS a) / ((n : ℝ) + 2 + 4 * bwS a)))
          - bwLam n S ^ 2
            * (4 * bwS a * ((n : ℝ) - 1) / ((n : ℝ) + 2 + 4 * bwS a) ^ 2) := by ring
    rw [hdist]
    linarith [hb]
  -- the Böhm–Wilking identity
  have ha1 : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0 := by
    have : (0 : ℝ) < 1 + 2 * ((n : ℝ) - 1) * a := by nlinarith
    exact ne_of_gt this
  have hb1 : 1 + ((n : ℝ) - 2) * (1 / 2) ≠ 0 := by
    have : (0 : ℝ) < 1 + ((n : ℝ) - 2) * (1 / 2) := by nlinarith
    exact ne_of_gt this
  have hX1 : linv a (1 / 2) (Q (ell a (1 / 2) S)) = Q S + bwCorr a (1 / 2) S := by
    rw [linv_Q_ell n a (1 / 2) ha1 hb1 hS, bwCorr]
    abel
  have hX : linv a (1 / 2) (Q (ell a (1 / 2) S)) = Q S + DtensorA n a S := by
    rw [hX1, bwCorr_half_eq n hn1 ha S]
  rw [hX, Q2P_EFun_add]
  have h1 : 0 ≤ Q2P.EFun (Q S) x y z w := inPIC2_Q_pointwise n S hS hP x y z w hdeg
  have hIso_pos : 0 < Q2P.EFun (Iso n) x y z w :=
    lt_of_le_of_ne (Cone.inPIC2_iso n x y z w) (Ne.symm hIso)
  have hid2sym : ∀ i j : Fin n, id2 n i j = id2 n j i := id2_symm_a n
  have hA := bwA_qform_nonneg n hn3 ha hric (le_of_lt hlam)
  have hAsym := bwA_symm n hS
  have hBq := bwB_qform_nonneg n hn3 ha hric
  have hBsym := bwB_symm n a hS
  have hRsym := ric0sq_symm n hS
  have hRq := ric0sq_qform_nonneg n hS
  have hT1 : 0 ≤ Q2P.EFun (knProd (bwA n S) (bwA n S)) x y z w :=
    EFun_knProd_psd n hAsym hAsym hA hA x y z w
  have hT2 : 0 ≤ Q2P.EFun (knProd (bwB n a S) (id2 n)) x y z w :=
    EFun_knProd_psd n hBsym hid2sym hBq
      (fun v => by simpa only [sum_id2_quad] using sum_id2_nonneg n v) x y z w
  have hT3 : 0 ≤ Q2P.EFun (knProd (ric0sq S) (id2 n)) x y z w :=
    EFun_knProd_psd n hRsym hid2sym hRq
      (fun v => by simpa only [sum_id2_quad] using sum_id2_nonneg n v) x y z w
  have hT4 : Q2P.EFun (knProd (id2 n) (id2 n)) x y z w = 2 * Q2P.EFun (Iso n) x y z w := by
    rw [knProd_id2_id2_a, Q2P_EFun_smul]
  have hgap : 2 * (bwLam n S ^ 2 * efaPsi n a) * Q2P.EFun (Iso n) x y z w
      ≤ bwGamma n a S * (2 * Q2P.EFun (Iso n) x y z w) := by
    have h2pos : (0 : ℝ) ≤ 2 * Q2P.EFun (Iso n) x y z w := by linarith
    have h := mul_le_mul_of_nonneg_right hG h2pos
    calc 2 * (bwLam n S ^ 2 * efaPsi n a) * Q2P.EFun (Iso n) x y z w
        = (bwLam n S ^ 2 * efaPsi n a) * (2 * Q2P.EFun (Iso n) x y z w) := by ring
      _ ≤ bwGamma n a S * (2 * Q2P.EFun (Iso n) x y z w) := h
  have hDt : 2 * (bwLam n S ^ 2 * efaPsi n a) * Q2P.EFun (Iso n) x y z w
      ≤ Q2P.EFun (DtensorA n a S) x y z w := by
    rw [DtensorA, Q2P_EFun_add, Q2P_EFun_add, Q2P_EFun_add, Q2P_EFun_smul, Q2P_EFun_smul,
      Q2P_EFun_smul, Q2P_EFun_smul, hT4]
    have hc1 : 0 ≤ ((n : ℝ) + 2) / 4 := by positivity
    have hc2 : 0 ≤ 2 * bwS a * bwLam n S := by positivity
    nlinarith [hT1, hT2, hT3, hgap, hc1, hc2]
  have hDt' : 2 * efaPsi n a * (scalAlg S / (n : ℝ)) ^ 2 * Q2P.EFun (Iso n) x y z w
      ≤ Q2P.EFun (DtensorA n a S) x y z w := by
    have he : 2 * (bwLam n S ^ 2 * efaPsi n a) * Q2P.EFun (Iso n) x y z w
        = 2 * efaPsi n a * (scalAlg S / (n : ℝ)) ^ 2 * Q2P.EFun (Iso n) x y z w := by
      rw [hlam']; ring
    rwa [he] at hDt
  linarith [h1, hDt']

/-! ## 6. The two-dimensional case

For `n = 2` every algebraic curvature tensor is a multiple of `Iso 2`, so both conjuncts of
`ShiftStrict` have contradictory hypotheses. -/

/-- Antisymmetry in the last pair of indices. -/
lemma anti34_chat {n : ℕ} {R : Curv4 n} (hR : IsAlgCurv R) (i j k l : Fin n) :
    R i j l k = - R i j k l := by
  have h1 : R i j l k = R l k i j := (hR.2.1 i j l k).symm
  have h2 : R l k i j = -R k l i j := by
    have h := hR.1 l k i j
    linarith
  have h3 : R k l i j = R i j k l := (hR.2.1 k l i j).symm
  linarith

/-- Every algebraic curvature tensor on `ℝ²` is a multiple of `Iso 2`. -/
lemma isAlgCurv_two_eq_smul_Iso {R : Submission.Diff.Alg.Curv4 2} (hR : IsAlgCurv R) :
    R = (R 0 1 0 1) • Iso 2 := by
  have h00 : ∀ k l : Fin 2, R 0 0 k l = 0 := by
    intro k l
    have h := hR.1 0 0 k l
    linarith
  have h11 : ∀ k l : Fin 2, R 1 1 k l = 0 := by
    intro k l
    have h := hR.1 1 1 k l
    linarith
  have hz : ∀ i j : Fin 2, R i j 0 0 = 0 := by
    intro i j
    have h := anti34_chat hR i j 0 0
    linarith
  have hz1 : ∀ i j : Fin 2, R i j 1 1 = 0 := by
    intro i j
    have h := anti34_chat hR i j 1 1
    linarith
  have hA : R 0 1 1 0 = -R 0 1 0 1 := anti34_chat hR 0 1 0 1
  have hB : R 1 0 0 1 = -R 0 1 0 1 := hR.1 0 1 0 1
  have hC : R 1 0 1 0 = R 0 1 0 1 := by
    have h := hR.1 1 0 1 0
    linarith [h, hA]
  funext i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp only [Iso, Pi.smul_apply, smul_eq_mul, Fin.isValue, Fin.reduceFinMk] <;>
    norm_num <;>
    (try simp only [h00, h11, hz, hz1]) <;>
    norm_num <;>
    linarith [hA, hB, hC]

/-- The `n = 2` case of `chat_shift_strict` (vacuous). -/
theorem chat_shift_strict_two (ε : ℝ) (hε : 0 < ε) :
    ∃ ĉ₀ : ℝ, 0 < ĉ₀ ∧ ∀ s : ℝ, ε ≤ s →
      ∀ X : Submission.Diff.Alg.Curv4 2, X ∈ Chat 2 s → scalAlg X = 1 →
        ∀ ĉ : ℝ, 0 < ĉ → ĉ ≤ ĉ₀ → ShiftStrict 2 s ĉ X := by
  refine ⟨1, one_pos, fun s hs X hX hscal ĉ hĉ0 _ => ?_⟩
  have hs' : 0 < s := lt_of_lt_of_le hε hs
  have hs0 : (0 : ℝ) ≤ s := le_of_lt hs'
  have hXc : X ∈ Ccone (n := 2) (chatAA 2 s) (chatBB s) (chatPP 2 s) := by
    rwa [← chat_eq_Ccone_param]
  obtain ⟨S, hS, hSeq⟩ := hXc
  have hSalg : IsAlgCurv S := hS.1
  have hSne : S ≠ 0 := by
    intro h0
    have hX0 : X = 0 := by rw [← hSeq, h0, ell_zero']
    rw [hX0, scalAlg_zero'] at hscal
    exact one_ne_zero hscal.symm
  obtain ⟨c, hc⟩ : ∃ c : ℝ, S = c • Iso 2 :=
    ⟨S 0 1 0 1, isAlgCurv_two_eq_smul_Iso hSalg⟩
  have hcne : c ≠ 0 := by
    intro h0
    exact hSne (by rw [hc, h0, zero_smul])
  have hsa : (0 : ℝ) < 1 + 2 * ((2 : ℝ) - 1) * chatAA 2 s := by
    have h1 : (0 : ℝ) ≤ chatAA 2 s := chatAA_nonneg 2 (by norm_num) hs0
    linarith
  have hsb : (0 : ℝ) < 1 + ((2 : ℝ) - 2) * chatBB s := by
    have h1 : (0 : ℝ) ≤ chatBB s := chatBB_nonneg hs0
    linarith
  have hchat : chatLinv 2 s X = S := by
    rw [chatLinv_eq_linv 2 (by norm_num) hs0, ← hSeq,
      linv_ell 2 (by norm_num) (ne_of_gt hsa) (ne_of_gt hsb) hSalg]
  have hricS : ∀ v' : Fin 2 → ℝ, (∑ i, ∑ j, ric S i j * v' i * v' j) = c * (∑ i, v' i * v' i) := by
    intro v'
    have hr : ric S = c • id2 2 := by
      ext i j
      rw [hc, ric_smul_linv, ric_iso]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [show (∑ i, ∑ j, ric S i j * v' i * v' j) = qform (ric S) v' from rfl, hr, qform_smul,
      qform_id2_eq]
  have hσS : scalAlg S = 2 * c := by
    rw [hc, scalAlg_smul, scalAlg_iso]
    ring
  refine ⟨?_, ?_⟩
  · intro v hv htight
    exfalso
    rw [hchat, hricS v, hσS] at htight
    have hp1 : chatPP 2 s < 1 := chatPP_lt_one 2 (by norm_num) hs'
    have hq : 0 < ∑ i, v i * v i := by
      obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
        by_contra h
        push_neg at h
        exact hv (funext fun i => h i)
      have hnn : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ v i * v i :=
        fun i _ => mul_self_nonneg (v i)
      have hle : v i₀ * v i₀ ≤ ∑ i, v i * v i := Finset.single_le_sum hnn (Finset.mem_univ i₀)
      have hlt : 0 < v i₀ * v i₀ := mul_self_pos.mpr hi₀
      linarith
    have h2 : chatPP 2 s * (∑ i, v i * v i) = ∑ i, v i * v i := by
      have h3 : c * (chatPP 2 s * (∑ i, v i * v i)) = c * (∑ i, v i * v i) := by
        linarith [htight]
      exact mul_left_cancel₀ hcne h3
    have h4 : (chatPP 2 s - 1) * (∑ i, v i * v i) = 0 := by linarith [h2]
    rcases mul_eq_zero.mp h4 with h5 | h5
    · linarith
    · linarith
  · intro x y z w hdeg hIso
    exfalso
    rw [hchat] at hdeg
    have h1 : Q2P.EFun S x y z w = c * Q2P.EFun (Iso 2) x y z w := by
      rw [hc, EFun_smul_lin]
    rw [h1] at hdeg
    exact hIso ((mul_eq_zero.mp hdeg).resolve_left hcne)


set_option maxHeartbeats 3200000 in
/-- The uniform lower bound for `efaPsi n a / (1 + 2(n-1)a)` used in the choice of `ĉ₀`. -/
theorem efaPsi_mul_lower (n : ℕ) (hn : 3 ≤ n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : ℝ, 1 / 2 < a →
      c ≤ Work.Diff.Alg.Pinch.efaPsi n a / (1 + 2 * ((n : ℝ) - 1) * a) := by
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0R : (0 : ℝ) < (n : ℝ) := by linarith
  have hDen : (0 : ℝ) < ((n : ℝ) + 2) * ((n : ℝ) + 6) ^ 2 * (2 * (n : ℝ) - 1) :=
    mul_pos (mul_pos (by linarith) (by positivity)) (by linarith)
  set Den : ℝ := ((n : ℝ) + 2) * ((n : ℝ) + 6) ^ 2 * (2 * (n : ℝ) - 1) with hDendef
  have hDenpos : 0 < Den := by rw [hDendef]; exact hDen
  set c0 : ℝ := min (min ((1 / 2) / Den) (min (60 / Den) (((n : ℝ) - 2) * ((n : ℝ) + 2) ^ 2 / Den)))
      (2 / ((n : ℝ) + 2) ^ 3) with hc0def
  have hc0pos : 0 < c0 := by
    rw [hc0def]
    exact lt_min (lt_min (div_pos (by norm_num) hDenpos)
      (lt_min (div_pos (by norm_num) hDenpos)
        (div_pos (mul_pos (by linarith) (by positivity)) hDenpos)))
      (div_pos (by norm_num) (by positivity))
  refine ⟨c0, hc0pos, fun a ha => ?_⟩
  set s : ℝ := 2 * a - 1 with hsdef
  set E : ℝ := (n : ℝ) + ((n : ℝ) - 1) * s with hE
  set D : ℝ := (n : ℝ) + 2 + 4 * s with hDdef
  have hs : 0 < s := by rw [hsdef]; linarith
  have hEpos : 0 < E := by rw [hE]; nlinarith
  have hDpos : 0 < D := by rw [hDdef]; linarith
  have hD2pos : (0 : ℝ) < D ^ 2 := by positivity
  have hden : 1 + 2 * ((n : ℝ) - 1) * a = E := by rw [hE, hsdef]; ring
  set X : ℝ := ((n : ℝ) + 2) * D ^ 2 with hXdef
  have hXpos : 0 < X := by rw [hXdef]; positivity
  have hN : efaPsi n a * ((n : ℝ) + 2) * D ^ 2
      = ((n : ℝ) - 2) * ((n : ℝ) + 2) ^ 2 + ((n : ℝ) + 2) * ((n : ℝ) ^ 2 - 24) * s
        + 8 * ((n : ℝ) - 2) * ((n : ℝ) + 4) * s ^ 2 + 16 * ((n : ℝ) + 2) * s ^ 3 := by
    rw [hDdef]
    rw [efaPsi, show (2 * a - 1) = s from hsdef.symm]
    field_simp
    ring_nf
  set Nn : ℝ := ((n : ℝ) - 2) * ((n : ℝ) + 2) ^ 2 + ((n : ℝ) + 2) * ((n : ℝ) ^ 2 - 24) * s
    + 8 * ((n : ℝ) - 2) * ((n : ℝ) + 4) * s ^ 2 + 16 * ((n : ℝ) + 2) * s ^ 3 with hNdef
  have hef : efaPsi n a = Nn / X := by
    rw [eq_div_iff (ne_of_gt hXpos), hNdef, hXdef, ← mul_assoc]
    exact hN
  have hcA : c0 ≤ (1 / 2) / Den := by
    rw [hc0def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hcB : c0 ≤ (60 / Den) := by
    rw [hc0def]; exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcC : c0 ≤ ((n : ℝ) - 2) * ((n : ℝ) + 2) ^ 2 / Den := by
    rw [hc0def]; exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hcD : c0 ≤ 2 / ((n : ℝ) + 2) ^ 3 := by rw [hc0def]; exact min_le_right _ _
  rw [hden, hef]
  have hgoal1 : c0 ≤ Nn / X / E := by
    rw [le_div_iff₀ hEpos, le_div_iff₀ hXpos]
    by_cases hs1 : s ≤ 1
    · -- small `s`
      have hE1 : E ≤ 2 * (n : ℝ) - 1 := by rw [hE]; nlinarith
      have hD1 : D ^ 2 ≤ ((n : ℝ) + 6) ^ 2 := by
        rw [hDdef]; nlinarith [sq_nonneg (4 * s - 2)]
      have hmul : E * X ≤ Den := by
        rw [hXdef, hDendef]
        have h1 : E * D ^ 2 ≤ (2 * (n : ℝ) - 1) * ((n : ℝ) + 6) ^ 2 :=
          mul_le_mul hE1 hD1 (by positivity) (by linarith)
        calc E * (((n : ℝ) + 2) * D ^ 2) = ((n : ℝ) + 2) * (E * D ^ 2) := by ring
          _ ≤ ((n : ℝ) + 2) * ((2 * (n : ℝ) - 1) * ((n : ℝ) + 6) ^ 2) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = ((n : ℝ) + 2) * ((n : ℝ) + 6) ^ 2 * (2 * (n : ℝ) - 1) := by ring
      rcases eq_or_lt_of_le hn with h3 | h3
      · subst h3
        have hN3 : (1 / 2 : ℝ) ≤ Nn := by
          rw [hNdef]
          norm_num
          nlinarith [sq_nonneg (s - 1 / 2), sq_nonneg (272 * s - 95), sq_nonneg (s - 3 / 8),
            sq_nonneg (s - 2 / 5), sq_nonneg (s - 1 / 3)]
        have hmain : c0 * (E * X) ≤ Nn := by
          calc c0 * (E * X) ≤ c0 * Den := mul_le_mul_of_nonneg_left hmul (le_of_lt hc0pos)
            _ ≤ ((1 / 2) / Den) * Den := mul_le_mul_of_nonneg_right hcA (le_of_lt hDenpos)
            _ = 1 / 2 := by rw [div_mul_cancel₀ _ (ne_of_gt hDenpos)]
            _ ≤ Nn := hN3
        nlinarith [hmain]
      · rcases eq_or_lt_of_le (show 4 ≤ n by omega) with h4 | h4
        · subst h4
          have hN4 : (60 : ℝ) ≤ Nn := by
            rw [hNdef]
            norm_num
            nlinarith [sq_nonneg (s - 1 / 5), sq_nonneg (128 * s - 24)]
          have hmain : c0 * (E * X) ≤ Nn := by
            calc c0 * (E * X) ≤ c0 * Den := mul_le_mul_of_nonneg_left hmul (le_of_lt hc0pos)
              _ ≤ (60 / Den) * Den := mul_le_mul_of_nonneg_right hcB (le_of_lt hDenpos)
              _ = 60 := by rw [div_mul_cancel₀ _ (ne_of_gt hDenpos)]
              _ ≤ Nn := hN4
          nlinarith [hmain]
        · have h5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h4
          have hc1 : (0 : ℝ) ≤ ((n : ℝ) + 2) * ((n : ℝ) ^ 2 - 24) * s :=
            mul_nonneg (mul_nonneg (by linarith) (by nlinarith)) (le_of_lt hs)
          have hc2 : (0 : ℝ) ≤ 8 * ((n : ℝ) - 2) * ((n : ℝ) + 4) * s ^ 2 :=
            mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith))
              (sq_nonneg s)
          have hc3 : (0 : ℝ) ≤ 16 * ((n : ℝ) + 2) * s ^ 3 :=
            mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (pow_nonneg (le_of_lt hs) 3)
          have hN5 : ((n : ℝ) - 2) * ((n : ℝ) + 2) ^ 2 ≤ Nn := by rw [hNdef]; linarith
          have hmain : c0 * (E * X) ≤ Nn := by
            calc c0 * (E * X) ≤ c0 * Den := mul_le_mul_of_nonneg_left hmul (le_of_lt hc0pos)
              _ ≤ (((n : ℝ) - 2) * ((n : ℝ) + 2) ^ 2 / Den) * Den :=
                  mul_le_mul_of_nonneg_right hcC (le_of_lt hDenpos)
              _ = ((n : ℝ) - 2) * ((n : ℝ) + 2) ^ 2 := by
                  rw [div_mul_cancel₀ _ (ne_of_gt hDenpos)]
              _ ≤ Nn := hN5
          nlinarith [hmain]
    · -- `1 ≤ s`
      push_neg at hs1
      have hs1' : (1 : ℝ) ≤ s := le_of_lt hs1
      have hD1 : D ≤ ((n : ℝ) + 2) * (1 + s) := by rw [hDdef]; nlinarith
      have hE1 : E ≤ ((n : ℝ) + 2) * (1 + s) := by rw [hE]; nlinarith
      have hmul : E * X ≤ ((n : ℝ) + 2) ^ 4 * (1 + s) ^ 3 := by
        rw [hXdef]
        have hD2 : D ^ 2 ≤ (((n : ℝ) + 2) * (1 + s)) ^ 2 := by nlinarith [hD1, hDpos]
        have h1 : E * D ^ 2 ≤ (((n : ℝ) + 2) * (1 + s)) ^ 3 := by
          calc E * D ^ 2 ≤ (((n : ℝ) + 2) * (1 + s)) * (((n : ℝ) + 2) * (1 + s)) ^ 2 :=
                mul_le_mul hE1 hD2 (by positivity) (by positivity)
            _ = (((n : ℝ) + 2) * (1 + s)) ^ 3 := by ring
        calc E * (((n : ℝ) + 2) * D ^ 2) = ((n : ℝ) + 2) * (E * D ^ 2) := by ring
          _ ≤ ((n : ℝ) + 2) * ((((n : ℝ) + 2) * (1 + s)) ^ 3) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = ((n : ℝ) + 2) ^ 4 * (1 + s) ^ 3 := by ring
      have hN6 : 16 * ((n : ℝ) + 2) * s ^ 3 ≤ Nn := by
        rw [hNdef]
        rcases eq_or_lt_of_le hn with h3 | h3
        · subst h3
          norm_num
          nlinarith [mul_nonneg (sub_nonneg.mpr hs1') (by linarith : (0 : ℝ) ≤ 56 * s - 19)]
        · rcases eq_or_lt_of_le (show 4 ≤ n by omega) with h4 | h4
          · subst h4
            norm_num
            nlinarith [sq_nonneg (s - 3 / 16)]
          · have h5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h4
            have hc1 : (0 : ℝ) ≤ ((n : ℝ) + 2) * ((n : ℝ) ^ 2 - 24) * s :=
              mul_nonneg (mul_nonneg (by linarith) (by nlinarith)) (le_of_lt hs)
            have hc2 : (0 : ℝ) ≤ 8 * ((n : ℝ) - 2) * ((n : ℝ) + 4) * s ^ 2 :=
              mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith))
                (sq_nonneg s)
            have hc0' : (0 : ℝ) ≤ ((n : ℝ) - 2) * ((n : ℝ) + 2) ^ 2 :=
              mul_nonneg (by linarith) (by positivity)
            linarith
      have hpow : ((1 : ℝ) + s) ^ 3 ≤ ((2 * s) ^ 3) := by
        have h2 : 1 + s ≤ 2 * s := by linarith
        exact pow_le_pow_left₀ (by positivity) h2 3
      have hmain : c0 * (E * X) ≤ Nn := by
        calc c0 * (E * X) ≤ c0 * (((n : ℝ) + 2) ^ 4 * (1 + s) ^ 3) :=
              mul_le_mul_of_nonneg_left hmul (le_of_lt hc0pos)
          _ ≤ (2 / ((n : ℝ) + 2) ^ 3) * (((n : ℝ) + 2) ^ 4 * (1 + s) ^ 3) :=
              mul_le_mul_of_nonneg_right hcD (by positivity)
          _ = 2 * ((n : ℝ) + 2) * (1 + s) ^ 3 := by
              field_simp
          _ ≤ 2 * ((n : ℝ) + 2) * ((2 * s) ^ 3) := by
              have hpos : (0 : ℝ) < 2 * ((n : ℝ) + 2) := by positivity
              exact mul_le_mul_of_nonneg_left hpow hpos.le
          _ = 16 * ((n : ℝ) + 2) * s ^ 3 := by ring
          _ ≤ Nn := hN6
      nlinarith [hmain]
  exact hgoal1

/-! ## 7. The shifted reaction direction and its quantitative bounds -/

/-- `A₂ = 1 + 2(n-1)a`: the factor by which `scalAlg` scales under `ell a b`. -/
noncomputable def A2shift (n : ℕ) (a : ℝ) : ℝ := 1 + 2 * ((n : ℝ) - 1) * a

/-- The scalar factor `2(n-1)/A₂` of the quadratic term in the shift. -/
noncomputable def shiftMu (n : ℕ) (A2 : ℝ) : ℝ := ((2 * (n - 1) : ℕ) : ℝ) * (1 / A2)

/-- `linv a b (Q (ell a b S))`: the unshifted reaction direction of `ell a b S`. -/
noncomputable def shiftW0 (n : ℕ) (a b : ℝ) (S : Curv4 n) : Curv4 n := linv a b (Q (ell a b S))

/-- `linv a b (knProd (ric (ell a b S)) (id2 n))`: the linear perturbation of the shift. -/
noncomputable def shiftM (n : ℕ) (a b : ℝ) (S : Curv4 n) : Curv4 n :=
  linv a b (knProd (ric (ell a b S)) (id2 n))

/-- `linv a b (knProd (ric0 S) (id2 n))`: the traceless part of the perturbation. -/
noncomputable def shiftN (n : ℕ) (a b : ℝ) (S : Curv4 n) : Curv4 n :=
  linv a b (knProd (ric0 S) (id2 n))

lemma ricMarg_sub (T T' : Curv4 n) (p : ℝ) (v : Fin n → ℝ) :
    ricMarg (T - T') p v = ricMarg T p v - ricMarg T' p v := by
  have hric : ric (T - T') = ric T - ric T' :=
    funext fun i => funext fun j => ric_sub T T' i j
  simp only [ricMarg]
  rw [hric, scalAlg_sub, qform_sub]
  ring

/-- The trivial bound `|ricMarg T p v| ≤ (n² + n²|p|) ‖T‖ |v|²`. -/
lemma ricMarg_abs_le (n : ℕ) (hn : 2 ≤ n) (T : Curv4 n) (p : ℝ) (v : Fin n → ℝ) :
    |ricMarg T p v| ≤ ((n : ℝ) ^ 2 + (n : ℝ) ^ 2 * |p|) * ‖T‖ * (∑ i, v i * v i) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hsv : (0 : ℝ) ≤ ∑ i, v i * v i := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have h1 : |∑ i, ∑ j, ric T i j * v i * v j| ≤ (n : ℝ) ^ 2 * ‖T‖ * (∑ i, v i * v i) := by
    have e1 : |∑ i, ∑ j, ric T i j * v i * v j|
        ≤ ∑ i, ∑ j, (n : ℝ) * ‖T‖ * (|v i| * |v j|) := by
      calc |∑ i, ∑ j, ric T i j * v i * v j|
          ≤ ∑ i, |∑ j, ric T i j * v i * v j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, ∑ j, |ric T i j * v i * v j| :=
            Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
        _ ≤ ∑ i, ∑ j, (n : ℝ) * ‖T‖ * (|v i| * |v j|) := by
            apply Finset.sum_le_sum; intro i _
            apply Finset.sum_le_sum; intro j _
            calc |ric T i j * v i * v j| = |ric T i j| * (|v i| * |v j|) := by
                  rw [abs_mul, abs_mul]; ring
              _ ≤ ((n : ℝ) * ‖T‖) * (|v i| * |v j|) :=
                  mul_le_mul_of_nonneg_right (chat_linv_abs_ric T i j)
                    (mul_nonneg (abs_nonneg _) (abs_nonneg _))
              _ = (n : ℝ) * ‖T‖ * (|v i| * |v j|) := by ring
    have e2 : (∑ i, ∑ j, (n : ℝ) * ‖T‖ * (|v i| * |v j|))
        = (n : ℝ) * ‖T‖ * ((∑ i, |v i|) * (∑ i, |v i|)) := by
      calc ∑ i, ∑ j, (n : ℝ) * ‖T‖ * (|v i| * |v j|)
          = ∑ i, (n : ℝ) * ‖T‖ * (|v i| * (∑ j, |v j|)) := by
            apply Finset.sum_congr rfl; intro i _
            rw [← Finset.mul_sum, ← Finset.mul_sum]
        _ = (n : ℝ) * ‖T‖ * (∑ i, |v i| * (∑ j, |v j|)) := by rw [← Finset.mul_sum]
        _ = (n : ℝ) * ‖T‖ * ((∑ i, |v i|) * (∑ j, |v j|)) := by rw [← Finset.sum_mul]
        _ = (n : ℝ) * ‖T‖ * ((∑ i, |v i|) * (∑ i, |v i|)) := rfl
    have e3 : (∑ i, |v i|) * (∑ i, |v i|) ≤ (n : ℝ) * (∑ i, v i * v i) := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
        (fun _ : Fin n => (1 : ℝ)) (fun i => |v i|)
      have h3 : (∑ i, |v i| ^ 2) = ∑ i, v i * v i := by
        apply Finset.sum_congr rfl; intro i _
        rw [sq_abs, pow_two]
      have h4 : ((∑ i, |v i|)) ^ 2 ≤ (n : ℝ) * (∑ i, v i * v i) := by
        simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_one, h3] using hcs
      calc (∑ i, |v i|) * (∑ i, |v i|) = (∑ i, |v i|) ^ 2 := by ring
        _ ≤ _ := h4
    calc |∑ i, ∑ j, ric T i j * v i * v j| ≤ ∑ i, ∑ j, (n : ℝ) * ‖T‖ * (|v i| * |v j|) := e1
      _ = (n : ℝ) * ‖T‖ * ((∑ i, |v i|) * (∑ i, |v i|)) := e2
      _ ≤ (n : ℝ) * ‖T‖ * ((n : ℝ) * (∑ i, v i * v i)) :=
          mul_le_mul_of_nonneg_left e3 (by positivity)
      _ = (n : ℝ) ^ 2 * ‖T‖ * (∑ i, v i * v i) := by ring
  have h2 : |(p * scalAlg T / (n : ℝ)) * (∑ i, v i * v i)|
      ≤ ((n : ℝ) * |p|) * ‖T‖ * (∑ i, v i * v i) := by
    have hsc : |scalAlg T| ≤ (n : ℝ) ^ 2 * ‖T‖ := chat_linv_abs_scalAlg T
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hnabs : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
    have h4 : |p * scalAlg T / (n : ℝ)| ≤ (n : ℝ) * |p| * ‖T‖ := by
      rw [abs_div, abs_mul]
      rw [hnabs]
      rw [div_le_iff₀ hn0]
      calc |p| * |scalAlg T| ≤ |p| * ((n : ℝ) ^ 2 * ‖T‖) :=
            mul_le_mul_of_nonneg_left hsc (abs_nonneg _)
        _ = ((n : ℝ) * |p| * ‖T‖) * (n : ℝ) := by ring
    calc |(p * scalAlg T / (n : ℝ)) * (∑ i, v i * v i)|
        = |p * scalAlg T / (n : ℝ)| * |∑ i, v i * v i| := by rw [abs_mul]
      _ ≤ ((n : ℝ) * |p| * ‖T‖) * |∑ i, v i * v i| :=
          mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
      _ = ((n : ℝ) * |p|) * ‖T‖ * (∑ i, v i * v i) := by
          rw [abs_of_nonneg hsv]
  rw [ricMarg]
  calc |qform (ric T) v - (p * scalAlg T / (n : ℝ)) * qform (id2 n) v|
      = |(∑ i, ∑ j, ric T i j * v i * v j)
          - (p * scalAlg T / (n : ℝ)) * (∑ i, v i * v i)| := by
        rw [qform, qform_id2_eq]
    _ ≤ |∑ i, ∑ j, ric T i j * v i * v j|
          + |(p * scalAlg T / (n : ℝ)) * (∑ i, v i * v i)| := abs_sub _ _
    _ ≤ (n : ℝ) ^ 2 * ‖T‖ * (∑ i, v i * v i)
          + ((n : ℝ) * |p|) * ‖T‖ * (∑ i, v i * v i) := add_le_add h1 h2
    _ ≤ ((n : ℝ) ^ 2 + (n : ℝ) ^ 2 * |p|) * ‖T‖ * (∑ i, v i * v i) := by
        have h5 : (n : ℝ) * |p| ≤ (n : ℝ) ^ 2 * |p| := by
          have hn1' : (1 : ℝ) ≤ (n : ℝ) := by linarith
          have h7 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right h7 (abs_nonneg p)
        have h8 : (n : ℝ) * |p| * ‖T‖ * (∑ i, v i * v i)
            ≤ (n : ℝ) ^ 2 * |p| * ‖T‖ * (∑ i, v i * v i) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h5 (norm_nonneg T)) hsv
        rw [add_mul, add_mul]
        linarith [h8]

/-- The decomposition of the shift perturbation. -/
lemma shiftM_decomp (n : ℕ) (hn : 2 ≤ n) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {S : Curv4 n} (hS : IsAlgCurv S) (hsc : scalAlg (ell a b S) = 1) :
    shiftM n a b S = (1 + ((n : ℝ) - 2) * b) • shiftN n a b S
      + (2 / ((n : ℝ) * A2shift n a)) • Iso n := by
  have h := linv_knProd_ric_decomp (n := n) (a := a) (b := b) (S := S)
    (Y := ell a b S) hn ha hb hS rfl hsc
  simpa only [shiftM, shiftN, A2shift] using h

/-- The norm bound `‖M‖ ≤ 2/(nA₂) + (1+(n-2)b) K_E (1-p) σ` for the shift perturbation. -/
theorem norm_shiftM_le (n : ℕ) (hn : 3 ≤ n) {a b p σ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hb' : b ≤ 1 / 2) (hp : p ≤ 1) (hσ : 0 < σ) {S : Curv4 n} (hS : IsAlgCurv S)
    (hric : RicPinch p S) (hsc : scalAlg S = σ) (hA2 : A2shift n a * σ = 1) :
    ‖shiftM n a b S‖ ≤ 2 / ((n : ℝ) * A2shift n a)
      + (1 + ((n : ℝ) - 2) * b) * cssKE n * (1 - p) * σ := by
  have hn2 : 2 ≤ n := by omega
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hA2ne : A2shift n a ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hA2
    exact one_ne_zero hA2.symm
  have hA2pos : 0 < A2shift n a := by
    rw [A2shift]
    nlinarith [ha]
  have hsc2 : scalAlg (ell a b S) = 1 := by
    rw [scalAlg_ell, hsc]
    simpa only [A2shift] using hA2
  have hdec := shiftM_decomp n hn2 ha hb hS hsc2
  rw [hdec]
  have h1mp : (0 : ℝ) ≤ 1 - p := by linarith
  have hcssKE : 0 ≤ cssKE n := by
    rw [cssKE]
    have h2 : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) * ((n : ℝ) - 1)) := Real.sqrt_nonneg _
    have h3 : (0 : ℝ) < (n : ℝ) := by linarith
    have h1 : (0 : ℝ) ≤ 10 * (n : ℝ) + 1 := by linarith
    positivity
  have hN : ‖shiftN n a b S‖ ≤ cssKE n * (1 - p) * σ := by
    have h := norm_linv_knProd_ric0_le n hn2 hp hσ hS hric hsc a b ha hb hb'
    simpa only [shiftN] using h
  have hc1 : (0 : ℝ) ≤ 1 + ((n : ℝ) - 2) * b := by nlinarith [hb]
  have hc2 : (0 : ℝ) ≤ 2 / ((n : ℝ) * A2shift n a) := by positivity
  have hA : ‖(1 + ((n : ℝ) - 2) * b) • shiftN n a b S‖
      ≤ (1 + ((n : ℝ) - 2) * b) * (cssKE n * (1 - p) * σ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc1]
    exact mul_le_mul_of_nonneg_left hN hc1
  have hB : ‖(2 / ((n : ℝ) * A2shift n a)) • Iso n‖ ≤ 2 / ((n : ℝ) * A2shift n a) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc2]
    calc (2 / ((n : ℝ) * A2shift n a)) * ‖Iso n‖
        ≤ (2 / ((n : ℝ) * A2shift n a)) * 1 :=
          mul_le_mul_of_nonneg_left (norm_Iso_le_one n) hc2
      _ = 2 / ((n : ℝ) * A2shift n a) := by ring
  calc ‖(1 + ((n : ℝ) - 2) * b) • shiftN n a b S
        + (2 / ((n : ℝ) * A2shift n a)) • Iso n‖
      ≤ ‖(1 + ((n : ℝ) - 2) * b) • shiftN n a b S‖
        + ‖(2 / ((n : ℝ) * A2shift n a)) • Iso n‖ := norm_add_le _ _
    _ ≤ (1 + ((n : ℝ) - 2) * b) * (cssKE n * (1 - p) * σ)
        + 2 / ((n : ℝ) * A2shift n a) := add_le_add hA hB
    _ = 2 / ((n : ℝ) * A2shift n a)
        + (1 + ((n : ℝ) - 2) * b) * cssKE n * (1 - p) * σ := by ring

/-- The quantitative Ricci-form bound for the shift perturbation:
`|ricMarg M p v| ≤ K_P (1-p) |v|² / A₂`. -/
theorem ricMarg_shiftM_le (n : ℕ) (hn : 3 ≤ n) {a b p σ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hb' : b ≤ 1 / 2) (hp : p ≤ 1) (hpm : -1 ≤ p) (hσ : 0 < σ) {S : Curv4 n}
    (hS : IsAlgCurv S) (hric : RicPinch p S) (hsc : scalAlg S = σ)
    (hA2 : A2shift n a * σ = 1) (v : Fin n → ℝ) :
    |ricMarg (shiftM n a b S) p v| ≤ cssKP n * (1 - p) / A2shift n a * (∑ i, v i * v i) := by
  have hn2 : 2 ≤ n := by omega
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hn0R : (0 : ℝ) < (n : ℝ) := by linarith
  have hA2pos : 0 < A2shift n a := by rw [A2shift]; nlinarith [ha]
  have hA2ne : A2shift n a ≠ 0 := ne_of_gt hA2pos
  have hσeq : σ = 1 / A2shift n a := by
    rw [eq_div_iff hA2ne, mul_comm]
    exact hA2
  have hsc2 : scalAlg (ell a b S) = 1 := by
    rw [scalAlg_ell, hsc]
    simpa only [A2shift] using hA2
  have hdec := shiftM_decomp n hn2 ha hb hS hsc2
  have hsv : (0 : ℝ) ≤ ∑ i, v i * v i := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have h1mp : (0 : ℝ) ≤ 1 - p := by linarith
  have hcssKE : 0 ≤ cssKE n := by
    rw [cssKE]
    have h2 : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) * ((n : ℝ) - 1)) := Real.sqrt_nonneg _
    have h1 : (0 : ℝ) ≤ 10 * (n : ℝ) + 1 := by linarith
    positivity
  have hp1 : |p| ≤ 1 := abs_le.mpr ⟨hpm, hp⟩
  have hN : ‖shiftN n a b S‖ ≤ cssKE n * (1 - p) * σ := by
    have h := norm_linv_knProd_ric0_le n hn2 hp hσ hS hric hsc a b ha hb hb'
    simpa only [shiftN] using h
  have hlin : ricMarg (shiftM n a b S) p v
      = (1 + ((n : ℝ) - 2) * b) * ricMarg (shiftN n a b S) p v
        + (2 / ((n : ℝ) * A2shift n a)) * ricMarg (Iso n) p v := by
    rw [hdec, ricMarg_add, ricMarg_smul, ricMarg_smul]
  have hIso : ricMarg (Iso n) p v = ((n : ℝ) - 1) * (1 - p) * (∑ i, v i * v i) :=
    ricMarg_Iso hn2 p v
  have hIso_nn : (0 : ℝ) ≤ ricMarg (Iso n) p v := by
    rw [hIso]
    have h1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
    exact mul_nonneg (mul_nonneg h1 h1mp) hsv
  have habsN : |ricMarg (shiftN n a b S) p v| ≤ 2 * (n : ℝ) ^ 2 * (cssKE n * (1 - p) * σ)
      * (∑ i, v i * v i) := by
    have h1 := ricMarg_abs_le n hn2 (shiftN n a b S) p v
    have h2 : ‖shiftN n a b S‖ ≤ cssKE n * (1 - p) * σ := hN
    calc |ricMarg (shiftN n a b S) p v|
        ≤ ((n : ℝ) ^ 2 + (n : ℝ) ^ 2 * |p|) * ‖shiftN n a b S‖ * (∑ i, v i * v i) := h1
      _ ≤ ((n : ℝ) ^ 2 + (n : ℝ) ^ 2 * 1) * (cssKE n * (1 - p) * σ)
            * (∑ i, v i * v i) := by
          have hc : ((n : ℝ) ^ 2 + (n : ℝ) ^ 2 * |p|) ≤ ((n : ℝ) ^ 2 + (n : ℝ) ^ 2 * 1) := by
            nlinarith [hp1]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hc h2 (norm_nonneg _) (by positivity)) hsv
      _ = 2 * (n : ℝ) ^ 2 * (cssKE n * (1 - p) * σ) * (∑ i, v i * v i) := by ring
  have hc1 : (0 : ℝ) ≤ 1 + ((n : ℝ) - 2) * b := by nlinarith [hb]
  have hc2 : (0 : ℝ) ≤ 2 / ((n : ℝ) * A2shift n a) := by positivity
  have hfinal : (1 + ((n : ℝ) - 2) * b) * (2 * (n : ℝ) ^ 2 * (cssKE n * (1 - p) * σ)
        * (∑ i, v i * v i))
      + (2 / ((n : ℝ) * A2shift n a)) * (((n : ℝ) - 1) * (1 - p) * (∑ i, v i * v i))
      ≤ cssKP n * (1 - p) / A2shift n a * (∑ i, v i * v i) := by
    have hCeq : cssKP n * (1 - p) / A2shift n a * (∑ i, v i * v i)
        = (cssKP n * (1 - p) * (∑ i, v i * v i)) / A2shift n a := by
      rw [div_mul_eq_mul_div]
    rw [hCeq, hσeq, cssKP, le_div_iff₀ hA2pos]
    have hL : ((1 + ((n : ℝ) - 2) * b)
            * (2 * (n : ℝ) ^ 2 * (cssKE n * (1 - p) * (1 / A2shift n a))
              * (∑ i, v i * v i))
          + (2 / ((n : ℝ) * A2shift n a)) * (((n : ℝ) - 1) * (1 - p) * (∑ i, v i * v i)))
          * A2shift n a
        = (1 + ((n : ℝ) - 2) * b) * (2 * (n : ℝ) ^ 2 * cssKE n * (1 - p)
            * (∑ i, v i * v i))
          + 2 * ((n : ℝ) - 1) * (1 - p) * (∑ i, v i * v i) / (n : ℝ) := by
      field_simp
    rw [hL]
    have hle : (1 + ((n : ℝ) - 2) * b) ≤ 1 + ((n : ℝ) - 2) / 2 := by
      have h2 : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith
      nlinarith [hb']
    have hkey : (1 + ((n : ℝ) - 2) * b) * (2 * (n : ℝ) ^ 2 * cssKE n * (1 - p)
          * (∑ i, v i * v i))
        ≤ (1 + ((n : ℝ) - 2) / 2) * (2 * (n : ℝ) ^ 2 * cssKE n * (1 - p)
          * (∑ i, v i * v i)) := by
      apply mul_le_mul_of_nonneg_right hle
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hcssKE)
        h1mp) hsv
    have hlasteq : 2 * ((n : ℝ) - 1) * (1 - p) * (∑ i, v i * v i) / (n : ℝ)
        = 2 * ((n : ℝ) - 1) / (n : ℝ) * (1 - p) * (∑ i, v i * v i) := by
      rw [div_eq_mul_inv]; ring
    calc (1 + ((n : ℝ) - 2) * b) * (2 * (n : ℝ) ^ 2 * cssKE n * (1 - p)
            * (∑ i, v i * v i))
          + 2 * ((n : ℝ) - 1) * (1 - p) * (∑ i, v i * v i) / (n : ℝ)
        ≤ (1 + ((n : ℝ) - 2) / 2) * (2 * (n : ℝ) ^ 2 * cssKE n * (1 - p)
            * (∑ i, v i * v i))
          + 2 * ((n : ℝ) - 1) / (n : ℝ) * (1 - p) * (∑ i, v i * v i) :=
          add_le_add hkey (le_of_eq hlasteq)
      _ = (2 * ((n : ℝ) - 1) / (n : ℝ)
            + (1 + ((n : ℝ) - 2) / 2) * (2 * (n : ℝ) ^ 2) * cssKE n) * (1 - p)
          * (∑ i, v i * v i) := by ring
  rw [hlin]
  calc |(1 + ((n : ℝ) - 2) * b) * ricMarg (shiftN n a b S) p v
        + (2 / ((n : ℝ) * A2shift n a)) * ricMarg (Iso n) p v|
      ≤ |(1 + ((n : ℝ) - 2) * b) * ricMarg (shiftN n a b S) p v|
        + |(2 / ((n : ℝ) * A2shift n a)) * ricMarg (Iso n) p v| := abs_add_le _ _
    _ = (1 + ((n : ℝ) - 2) * b) * |ricMarg (shiftN n a b S) p v|
        + (2 / ((n : ℝ) * A2shift n a)) * |ricMarg (Iso n) p v| := by
        rw [abs_mul, abs_of_nonneg hc1, abs_mul, abs_of_nonneg hc2]
    _ ≤ (1 + ((n : ℝ) - 2) * b) * (2 * (n : ℝ) ^ 2 * (cssKE n * (1 - p) * σ)
          * (∑ i, v i * v i))
        + (2 / ((n : ℝ) * A2shift n a)) * (((n : ℝ) - 1) * (1 - p) * (∑ i, v i * v i)) := by
        rw [abs_of_nonneg hIso_nn]
        exact add_le_add (mul_le_mul_of_nonneg_left habsN hc1)
          (mul_le_mul_of_nonneg_left (le_of_eq hIso) hc2)
    _ ≤ cssKP n * (1 - p) / A2shift n a * (∑ i, v i * v i) := hfinal

/-! ## 8. The uniform thresholds -/

/-- The perturbation coefficient of the `PIC2` estimate: `2/n + (1+(n-2)/2) K_E`. -/
noncomputable def cssKFlux (n : ℕ) : ℝ :=
  2 / (n : ℝ) + (1 + ((n : ℝ) - 2) / 2) * cssKE n

/-- The threshold `ĉ₀` of the branch `0 < s ≤ 1/2` for the Ricci-form estimate. -/
noncomputable def cShiftB (n : ℕ) (cρ : ℝ) : ℝ :=
  4 * cρ / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4 * cssKP n)

/-- The parameter lower bound `φ(n)` of the branch `1/2 < s` for the Ricci-form estimate. -/
noncomputable def phiShiftA (n : ℕ) : ℝ :=
  min (1 / (2 * (n : ℝ))) (4 * (n : ℝ) / (((n : ℝ) + 6) ^ 2 * (2 * (n : ℝ) - 1) ^ 2))

/-- The threshold `ĉ₀` of the branch `1/2 < s` for the Ricci-form estimate. -/
noncomputable def cShiftA1 (n : ℕ) : ℝ := phiShiftA n / (2 * (n : ℝ) ^ 2 * cssKP n)

/-- The threshold `ĉ₀` of the branch `0 < s ≤ 1/2` for the `PIC2` estimate. -/
noncomputable def cShiftB2 (n : ℕ) (ε : ℝ) : ℝ :=
  16 * ((n : ℝ) - 2) * ε ^ 3 / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 5 * cssKFlux n)

/-- The threshold `ĉ₀` of the branch `1/2 < s` for the `PIC2` estimate. -/
noncomputable def cShiftA2 (n : ℕ) (c : ℝ) : ℝ := c / (2 * (n : ℝ) ^ 4 * cssKFlux n)

/-- The parameter lower bound of the branch `1/2 < s` for the Ricci-form estimate. -/
lemma phiShiftA_le (n : ℕ) (hn : 3 ≤ n) {a : ℝ} (ha : 1 / 2 < a) :
    phiShiftA n ≤ ((2 * a - 1) + (n : ℝ) * (4 / ((n : ℝ) - 2 + 8 * a)) ^ 2
        / (4 * (1 + 2 * ((n : ℝ) - 1) * a))) / (1 + 2 * ((n : ℝ) - 1) * a) := by
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by linarith
  have hA2pos : 0 < 1 + 2 * ((n : ℝ) - 1) * a := by nlinarith
  have hDpos : 0 < (n : ℝ) - 2 + 8 * a := by nlinarith
  have hX : (0 : ℝ) ≤ (n : ℝ) * (4 / ((n : ℝ) - 2 + 8 * a)) ^ 2
      / (4 * (1 + 2 * ((n : ℝ) - 1) * a)) := by positivity
  rcases lt_or_ge (1 : ℝ) a with h1 | h1
  · refine le_trans (min_le_left _ _) ?_
    rw [le_div_iff₀ hA2pos]
    have hA2le : 1 + 2 * ((n : ℝ) - 1) * a ≤ 2 * (n : ℝ) * a := by nlinarith
    have hstep : (1 / (2 * (n : ℝ))) * (1 + 2 * ((n : ℝ) - 1) * a) ≤ a := by
      calc (1 / (2 * (n : ℝ))) * (1 + 2 * ((n : ℝ) - 1) * a)
          ≤ (1 / (2 * (n : ℝ))) * (2 * (n : ℝ) * a) :=
            mul_le_mul_of_nonneg_left hA2le (by positivity)
        _ = a := by field_simp
    linarith [hstep, hX, h1]
  · refine le_trans (min_le_right _ _) ?_
    rw [le_div_iff₀ hA2pos]
    have hA2le : 1 + 2 * ((n : ℝ) - 1) * a ≤ 2 * (n : ℝ) - 1 := by nlinarith
    have hDle : (n : ℝ) - 2 + 8 * a ≤ (n : ℝ) + 6 := by linarith
    have h1pos : (0 : ℝ) < ((n : ℝ) + 6) ^ 2 * (2 * (n : ℝ) - 1) ^ 2 := by
      apply mul_pos
      · exact pow_pos (by linarith) 2
      · exact pow_pos (by linarith) 2
    have h2pos : (0 : ℝ) < ((n : ℝ) - 2 + 8 * a) ^ 2 * (1 + 2 * ((n : ℝ) - 1) * a) :=
      mul_pos (pow_pos hDpos 2) hA2pos
    have hkey : (4 * (n : ℝ) / (((n : ℝ) + 6) ^ 2 * (2 * (n : ℝ) - 1) ^ 2))
        * (1 + 2 * ((n : ℝ) - 1) * a)
        ≤ 4 * (n : ℝ) / (((n : ℝ) - 2 + 8 * a) ^ 2 * (1 + 2 * ((n : ℝ) - 1) * a)) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ h1pos h2pos]
      have hprod : ((1 + 2 * ((n : ℝ) - 1) * a) * ((n : ℝ) - 2 + 8 * a))
            * (((n : ℝ) - 2 + 8 * a) * (1 + 2 * ((n : ℝ) - 1) * a))
          ≤ ((2 * (n : ℝ) - 1) * ((n : ℝ) + 6)) * (((n : ℝ) + 6) * (2 * (n : ℝ) - 1)) := by
        have h1 : (1 + 2 * ((n : ℝ) - 1) * a) * ((n : ℝ) - 2 + 8 * a)
            ≤ (2 * (n : ℝ) - 1) * ((n : ℝ) + 6) :=
          mul_le_mul hA2le hDle hDpos.le (by linarith)
        have h1' : ((n : ℝ) - 2 + 8 * a) * (1 + 2 * ((n : ℝ) - 1) * a)
            ≤ ((n : ℝ) + 6) * (2 * (n : ℝ) - 1) :=
          mul_le_mul hDle hA2le hA2pos.le (by linarith)
        exact mul_le_mul h1 h1' (mul_nonneg hDpos.le hA2pos.le)
          (mul_nonneg (by linarith) (by linarith))
      nlinarith [hprod]
    have hstep2 : 4 * (n : ℝ) / (((n : ℝ) - 2 + 8 * a) ^ 2 * (1 + 2 * ((n : ℝ) - 1) * a))
        ≤ (2 * a - 1) + (n : ℝ) * (4 / ((n : ℝ) - 2 + 8 * a)) ^ 2
            / (4 * (1 + 2 * ((n : ℝ) - 1) * a)) := by
      have heq : (n : ℝ) * (4 / ((n : ℝ) - 2 + 8 * a)) ^ 2
            / (4 * (1 + 2 * ((n : ℝ) - 1) * a))
          = 4 * (n : ℝ) / (((n : ℝ) - 2 + 8 * a) ^ 2 * (1 + 2 * ((n : ℝ) - 1) * a)) := by
        field_simp
      have h2a : (0 : ℝ) ≤ 2 * a - 1 := by linarith
      linarith [heq.le, heq.ge, h2a]
    linarith [hkey, hstep2, hX]

/-! ## 9. Parameter bounds and thresholds used by the assembly of `chat_shift_strict` -/

noncomputable def cB2 (n : ℕ) (ε Cef : ℝ) : ℝ :=
  (16 * ((n : ℝ) - 2) * ε ^ 3 / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4)) / (Cef * cssKFlux n)

/-- The threshold for the branch `1/2 < s` and the `PIC2` estimate. -/
noncomputable def cA2 (n : ℕ) (Cef c : ℝ) : ℝ :=
  (c / (2 * (n : ℝ) ^ 2)) / (Cef * cssKFlux n)


/-! ## Elementary parameter bounds -/

lemma cssKP_pos {n : ℕ} (hn : 2 ≤ n) : 0 < cssKP n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h1 : (0 : ℝ) < 2 * ((n : ℝ) - 1) / (n : ℝ) := by
    apply div_pos _ hn0
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h2 : (0 : ℝ) ≤ cssKE n := by
    rw [cssKE]
    have h3 : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) * ((n : ℝ) - 1)) := Real.sqrt_nonneg _
    have h4 : (0 : ℝ) ≤ 10 * (n : ℝ) + 1 := by linarith
    positivity
  have h5 : (0 : ℝ) ≤ (1 + ((n : ℝ) - 2) / 2) * (2 * (n : ℝ) ^ 2) * cssKE n :=
    mul_nonneg (mul_nonneg (by linarith) (by positivity)) h2
  rw [cssKP]
  linarith

lemma cssKFlux_pos {n : ℕ} (hn : 3 ≤ n) : 0 < cssKFlux n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h2 : (0 : ℝ) ≤ cssKE n := by
    rw [cssKE]
    have h3 : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) * ((n : ℝ) - 1)) := Real.sqrt_nonneg _
    have h4 : (0 : ℝ) ≤ 10 * (n : ℝ) + 1 := by linarith
    positivity
  have h5 : (0 : ℝ) ≤ (1 + ((n : ℝ) - 2) / 2) * cssKE n := mul_nonneg (by linarith) h2
  rw [cssKFlux]
  have h6 : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  linarith

lemma phiShiftA_pos {n : ℕ} (hn : 3 ≤ n) : 0 < phiShiftA n := by
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [phiShiftA]
  apply lt_min
  · positivity
  · apply div_pos (by positivity)
    have h : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
    positivity

/-- `1 - ccP n s ≥ 4/(n+2)` for `0 < s ≤ 1/2`. -/
lemma one_sub_ccP_ge (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1 / 2) :
    4 / ((n : ℝ) + 2) ≤ 1 - ccP n s := by
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < 1 + ((n : ℝ) - 2) * s ^ 2 := by nlinarith [sq_nonneg s]
  have h1 : 1 - ccP n s = 1 / (1 + ((n : ℝ) - 2) * s ^ 2) := by
    rw [ccP]; ring
  rw [h1, le_div_iff₀ hpos, div_mul_eq_mul_div,
    div_le_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) + 2)]
  have hs2 : s ^ 2 ≤ 1 / 4 := by nlinarith [hs1, hs.le]
  nlinarith [hs2, sq_nonneg s]

/-- `ccA n b ≥ 4ε/(n+2)` on the window `[ε,1/2]`. -/
lemma ccA_lower (n : ℕ) (hn : 2 ≤ n) {ε b : ℝ} (hε : 0 < ε) (hb : ε ≤ b)
    (hb2 : b ≤ 1 / 2) : 4 * ε / ((n : ℝ) + 2) ≤ ccA n b := by
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hb0 : 0 < b := lt_of_lt_of_le hε hb
  have hden : (0 : ℝ) < 2 * (1 + ((n : ℝ) - 2) * b ^ 2) := by
    have := chatA_denom_pos hn b
    linarith
  have hstep : 4 * b / ((n : ℝ) + 2) ≤ ccA n b := by
    rw [ccA, div_le_div_iff₀ (by linarith) hden]
    have h3 : 0 ≤ (n : ℝ) + 2 - 8 * b := by linarith
    have h4 : 0 ≤ ((n : ℝ) - 2) * b * ((n : ℝ) + 2 - 8 * b) :=
      mul_nonneg (mul_nonneg (by linarith) hb0.le) h3
    nlinarith [h4]
  have hmul : 4 * ε / ((n : ℝ) + 2) ≤ 4 * b / ((n : ℝ) + 2) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  linarith [hmul, hstep]

/-- `ccP n b ≥ (n-2)ε²/(1+(n-2)/4)` on the window `[ε,1/2]`. -/
lemma ccP_lower (n : ℕ) (hn : 2 ≤ n) {ε b : ℝ} (hε : 0 < ε) (hb : ε ≤ b)
    (hb2 : b ≤ 1 / 2) :
    ((n : ℝ) - 2) * ε ^ 2 / (1 + ((n : ℝ) - 2) / 4) ≤ ccP n b := by
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hb0 : 0 < b := lt_of_lt_of_le hε hb
  have h1 : ((n : ℝ) - 2) * ε ^ 2 ≤ ((n : ℝ) - 2) * b ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    nlinarith [hε, hb, hε.le]
  have h2 : ((n : ℝ) - 2) * b ^ 2 ≤ ((n : ℝ) - 2) / 4 := by
    have h3 : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith
    have hb2sq : b ^ 2 ≤ 1 / 4 := by nlinarith [hb2, hb0.le]
    calc ((n : ℝ) - 2) * b ^ 2 ≤ ((n : ℝ) - 2) * (1 / 4) := mul_le_mul_of_nonneg_left hb2sq h3
      _ = ((n : ℝ) - 2) / 4 := by ring
  have hnum : (0 : ℝ) ≤ ((n : ℝ) - 2) * ε ^ 2 := mul_nonneg (by linarith) (sq_nonneg ε)
  have hden1 : (0 : ℝ) < 1 + ((n : ℝ) - 2) * b ^ 2 := by nlinarith [sq_nonneg b]
  have hden2 : (0 : ℝ) < 1 + ((n : ℝ) - 2) / 4 := by linarith
  have heq : 1 - 1 / (1 + ((n : ℝ) - 2) * b ^ 2)
      = ((n : ℝ) - 2) * b ^ 2 / (1 + ((n : ℝ) - 2) * b ^ 2) := by
    field_simp
    ring
  rw [ccP, heq, div_le_div_iff₀ hden2 hden1]
  nlinarith [h1, h2, hnum]

/-- `ccA n b · ccP n b ≥ 16(n-2)ε³/(n+2)²` on the window `[ε,1/2]`. -/
lemma ccA_ccP_ge (n : ℕ) (hn : 3 ≤ n) {ε b : ℝ} (hε : 0 < ε) (hb : ε ≤ b)
    (hb2 : b ≤ 1 / 2) :
    16 * ((n : ℝ) - 2) * ε ^ 3 / (((n : ℝ) + 2) ^ 2) ≤ ccA n b * ccP n b := by
  have hn2 : 2 ≤ n := by omega
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hA := ccA_lower n hn2 hε hb hb2
  have hP := ccP_lower n hn2 hε hb hb2
  have hA0 : (0 : ℝ) ≤ ccA n b := (ccA_pos (by omega) (lt_of_lt_of_le hε hb) hb2).le
  have hP2 : 4 * ((n : ℝ) - 2) * ε ^ 2 / ((n : ℝ) + 2) ≤ ccP n b := by
    have hd : 1 + ((n : ℝ) - 2) / 4 = ((n : ℝ) + 2) / 4 := by ring
    rw [hd] at hP
    have h4 : 0 < ((n : ℝ) + 2) / 4 := by linarith
    rw [div_le_iff₀ h4] at hP
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) + 2)]
    linarith [hP]
  calc 16 * ((n : ℝ) - 2) * ε ^ 3 / (((n : ℝ) + 2) ^ 2)
      = (4 * ε / ((n : ℝ) + 2)) * (4 * ((n : ℝ) - 2) * ε ^ 2 / ((n : ℝ) + 2)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, pow_two, mul_inv_rev]
        ring
    _ ≤ ccA n b * ccP n b := mul_le_mul hA hP2 (by positivity) hA0


end Work.Diff.Alg.Pinch
