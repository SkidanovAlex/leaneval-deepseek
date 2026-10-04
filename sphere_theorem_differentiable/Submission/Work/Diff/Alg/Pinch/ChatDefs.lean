import Mathlib
import Submission.Diff.Alg
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Chat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary definitions for `Work.Diff.Alg.Pinch.Chat_exhaust`

Two groups of definitions.

* `qfA`, `qfB`: the real and imaginary parts of the decomposable complex `2`-form `ζ ∧ η`,
  where `ζ = x + iy`, `η = z + iw`:
  `(ζ ∧ η)ᵢⱼ = qfA x y z w i j + i * qfB x y z w i j`.  These enter the quantitative form of the
  `PIC2` condition for *algebraic* curvature tensors:  for `IsAlgCurv D`,
  `4 * EF D x y z w = ∑ Dᵢⱼₖₗ (qfAᵢⱼ qfAₖₗ + qfBᵢⱼ qfBₖₗ)`
  (`Work.Diff.Alg.Pinch.Chat_quadform`), while
  `∑ (qfAᵢⱼ² + qfBᵢⱼ²) = 2 * EF (Iso n) x y z w` (`Work.Diff.Alg.Pinch.Chat_lagrange`).
  Together these show that `EF D` is controlled by `‖D‖ * EF (Iso n)` — i.e. that the round
  sphere is an *interior* point of the cone `{InPIC2}` inside the subspace of algebraic
  curvature tensors, which is what makes the cone family `Ĉ(s)` exhaust the interior.

* `chatA n s`, `chatP n s`: the parameters `a`, `p` of the Brendle–Schoen family
  `Ĉ(s) = ℓ_{a,s}(D(p))` for `0 < s ≤ 1/2` (see `Work.Diff.Alg.Pinch.Chat`), together with the
  elementary bounds used in the exhaustion argument.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- Real part of `(ζ ∧ η)ᵢⱼ` for `ζ = x + iy`, `η = z + iw`. -/
noncomputable def qfA (x y z w : Fin n → ℝ) (i j : Fin n) : ℝ :=
  (x i * z j - x j * z i) - (y i * w j - y j * w i)

/-- Imaginary part of `(ζ ∧ η)ᵢⱼ` for `ζ = x + iy`, `η = z + iw`. -/
noncomputable def qfB (x y z w : Fin n → ℝ) (i j : Fin n) : ℝ :=
  (x i * w j - x j * w i) + (y i * z j - y j * z i)

/-- The parameter `a` of the cone `Ĉ(s)` for `0 < s ≤ 1/2`. -/
noncomputable def chatA (n : ℕ) (s : ℝ) : ℝ :=
  (2 * s + ((n : ℝ) - 2) * s ^ 2) / (2 * (1 + ((n : ℝ) - 2) * s ^ 2))

/-- The parameter `p` of the cone `Ĉ(s)` for `0 < s ≤ 1/2`. -/
noncomputable def chatP (n : ℕ) (s : ℝ) : ℝ :=
  1 - 1 / (1 + ((n : ℝ) - 2) * s ^ 2)

lemma chat_c_nonneg {n : ℕ} (hn : 2 ≤ n) : (0 : ℝ) ≤ (n : ℝ) - 2 := by
  have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

/-- For `s ≤ 1/2` the family `Ĉ(s)` is the cone `ℓ_{a,s}(D(p))` with `a = chatA n s`, `p = chatP n s`. -/
theorem Chat_eq_Ccone (n : ℕ) {s : ℝ} (hs : s ≤ 1 / 2) :
    Chat n s = Ccone (n := n) (chatA n s) s (chatP n s) := by
  rw [Chat, if_pos hs, chatA, chatP]

lemma chatA_denom_pos {n : ℕ} (hn : 2 ≤ n) (s : ℝ) :
    0 < 1 + ((n : ℝ) - 2) * s ^ 2 := by
  have h2 := chat_c_nonneg hn
  nlinarith [sq_nonneg s]

lemma chatA_nonneg {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ chatA n s := by
  have hd := chatA_denom_pos hn s
  have h2 := chat_c_nonneg hn
  have hnum : 0 ≤ 2 * s + ((n : ℝ) - 2) * s ^ 2 := by nlinarith [sq_nonneg s]
  rw [chatA]
  exact div_nonneg hnum (by positivity)

lemma chatA_eq {n : ℕ} {s : ℝ} (hs : s ≠ 0) :
    chatA n s = s * (2 + ((n : ℝ) - 2) * s) / (2 * (1 + ((n : ℝ) - 2) * s ^ 2)) := by
  rw [chatA]
  field_simp

/-- The key elementary estimate: for `0 < s ≤ 1/2` the parameter `a` is `O(s)`. -/
lemma chatA_le {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2) :
    chatA n s ≤ s * (1 + ((n : ℝ) - 2) / 4) := by
  have hd := chatA_denom_pos hn s
  have h2 := chat_c_nonneg hn
  rw [chatA_eq hs.ne', div_le_iff₀ (by nlinarith [hd] : (0 : ℝ) < 2 * (1 + ((n : ℝ) - 2) * s ^ 2))]
  have key : (s * (1 + ((n : ℝ) - 2) / 4)) * (2 * (1 + ((n : ℝ) - 2) * s ^ 2))
      - (2 * s + ((n : ℝ) - 2) * s ^ 2)
      = ((n : ℝ) - 2) * s * (1 / 2 - s) + ((n : ℝ) - 2) * s ^ 3 * (2 + ((n : ℝ) - 2) / 2) := by
    ring
  have h1 : 0 ≤ ((n : ℝ) - 2) * s * (1 / 2 - s) :=
    mul_nonneg (mul_nonneg h2 hs.le) (by linarith)
  have h2' : 0 ≤ ((n : ℝ) - 2) * s ^ 3 * (2 + ((n : ℝ) - 2) / 2) :=
    mul_nonneg (mul_nonneg h2 (by positivity)) (by linarith)
  linarith [key, h1, h2']

lemma chatA_pos {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) : 0 < chatA n s := by
  have hd := chatA_denom_pos hn s
  have h2 := chat_c_nonneg hn
  have hnum : 0 < 2 * s + ((n : ℝ) - 2) * s ^ 2 := by nlinarith [sq_nonneg s]
  rw [chatA, div_pos_iff]
  exact Or.inl ⟨hnum, by positivity⟩

lemma chatP_eq_div {n : ℕ} (hn : 2 ≤ n) (s : ℝ) :
    chatP n s = (((n : ℝ) - 2) * s ^ 2) / (1 + ((n : ℝ) - 2) * s ^ 2) := by
  have hd := chatA_denom_pos hn s
  rw [chatP]
  field_simp
  ring

lemma chatP_nonneg {n : ℕ} (hn : 2 ≤ n) (s : ℝ) : 0 ≤ chatP n s := by
  have hd := chatA_denom_pos hn s
  have h2 := chat_c_nonneg hn
  rw [chatP_eq_div hn]
  exact div_nonneg (by positivity) (by linarith)

lemma chatP_le {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 ≤ s) :
    chatP n s ≤ ((n : ℝ) - 2) * s ^ 2 := by
  have hd := chatA_denom_pos hn s
  have h2 := chat_c_nonneg hn
  have hD : 0 ≤ ((n : ℝ) - 2) * s ^ 2 := by positivity
  rw [chatP_eq_div hn, div_le_iff₀ (by linarith : (0 : ℝ) < 1 + ((n : ℝ) - 2) * s ^ 2)]
  nlinarith [sq_nonneg (((n : ℝ) - 2) * s ^ 2), hs]

lemma chatP_lt_one {n : ℕ} (hn : 2 ≤ n) (s : ℝ) : chatP n s < 1 := by
  have hd := chatA_denom_pos hn s
  rw [chatP_eq_div hn]
  have hD : 0 ≤ ((n : ℝ) - 2) * s ^ 2 := by
    have h2 := chat_c_nonneg hn; positivity
  rw [div_lt_one (by linarith)]
  linarith

end Work.Diff.Alg.Pinch
