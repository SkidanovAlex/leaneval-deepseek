import Mathlib
import Submission.IntFun

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# ℓ₂-norm machinery for functions on ℤ (Section 3, Prop ell-2 update)

Tikhomirov 2020, Section 3.  `Lemma l:aux -98745220985-32` (the ℓ₂-drop lemma):
for `f,g ∈ ℓ₂(ℤ)` and `p ∈ (0,1)`, if `|{t : |f(t)−g(t)| ≥ κ}| ≥ k` then
`‖(1−p)f + p·g‖₂² ≤ (1−p)‖f‖₂² + p‖g‖₂² − p(1−p)·κ²·k`.

We provide:
- `norm₂sq f := ∑' t, (f t)^2`,
- translation invariance of `norm₂sq`,
- the pointwise quadratic identity underlying the drop,
- the norm-level identity `norm₂sq_mix_sub`,
- the drop lemma `l2_drop` (Finset formulation of the `≥ k` hypothesis).
-/

namespace Submission.L2Norm

open scoped BigOperators

/-- Square of the ℓ₂ norm over ℤ. -/
def norm₂sq (f : ℤ → ℝ) : ℝ := ∑' t : ℤ, (f t) ^ 2

/-- The mixture `(1−p)·f + p·g` as a function. -/
def mix (p : ℝ) (f g : ℤ → ℝ) : ℤ → ℝ :=
  fun t => (1 - p) * f t + p * g t

lemma norm₂sq_nonneg (f : ℤ → ℝ) : 0 ≤ norm₂sq f := by
  unfold norm₂sq
  exact tsum_nonneg (fun t => sq_nonneg _)

-- translation invariance of the square-norm
lemma summable_sq_translate_add {g : ℤ → ℝ} (c : ℤ) (hg : Summable (fun t : ℤ => (g t) ^ 2)) :
    Summable (fun t : ℤ => (g (t + c)) ^ 2) := by
  let e : ℤ ≃ ℤ := Equiv.addRight c
  have hcomp : (fun t : ℤ => (g (t + c)) ^ 2) = (fun t : ℤ => (g t) ^ 2) ∘ e := by
    funext t
    rfl
  rw [hcomp]
  exact (Equiv.summable_iff e).2 hg

lemma summable_sq_translate_sub {g : ℤ → ℝ} (c : ℤ) (hg : Summable (fun t : ℤ => (g t) ^ 2)) :
    Summable (fun t : ℤ => (g (t - c)) ^ 2) := by
  let e : ℤ ≃ ℤ := Equiv.subRight c
  have hcomp : (fun t : ℤ => (g (t - c)) ^ 2) = (fun t : ℤ => (g t) ^ 2) ∘ e := by
    funext t
    rfl
  rw [hcomp]
  exact (Equiv.summable_iff e).2 hg

lemma norm₂sq_translate_add {g : ℤ → ℝ} (c : ℤ) :
    norm₂sq (fun t : ℤ => g (t + c)) = norm₂sq g := by
  unfold norm₂sq
  let e : ℤ ≃ ℤ := Equiv.addRight c
  have hcomp : (fun t : ℤ => (g (t + c)) ^ 2) = (fun t : ℤ => (g t) ^ 2) ∘ e := by
    funext t
    rfl
  rw [hcomp]
  exact Equiv.tsum_eq e (fun t : ℤ => (g t) ^ 2)

lemma norm₂sq_translate_sub {g : ℤ → ℝ} (c : ℤ) :
    norm₂sq (fun t : ℤ => g (t - c)) = norm₂sq g := by
  unfold norm₂sq
  let e : ℤ ≃ ℤ := Equiv.subRight c
  have hcomp : (fun t : ℤ => (g (t - c)) ^ 2) = (fun t : ℤ => (g t) ^ 2) ∘ e := by
    funext t
    rfl
  rw [hcomp]
  exact Equiv.tsum_eq e (fun t : ℤ => (g t) ^ 2)

/-- Scalar multiplication preserves summability. -/
lemma summable_const_mul {f : ℤ → ℝ} (c : ℝ) (hf : Summable f) :
    Summable (fun t : ℤ => c * f t) := by
  rcases hf with ⟨a, ha⟩
  exact ⟨c * a, ha.mul_left c⟩

/-- The pointwise quadratic identity of the paper (line ~1040). -/
lemma sq_mix_eq (p a b : ℝ) :
    ((1 - p) * a + p * b) ^ 2 =
      (1 - p) * a ^ 2 + p * b ^ 2 - p * (1 - p) * (a - b) ^ 2 := by
  ring

/-- Pointwise bound `(a−b)² ≤ 2a² + 2b²`. -/
lemma sub_sq_le_two_sq (a b : ℝ) : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a + b)]

/-- `(f−g)²` is summable when `f²,g²` are. -/
lemma summable_sq_sub {f g : ℤ → ℝ}
    (hf2 : Summable (fun t : ℤ => (f t) ^ 2)) (hg2 : Summable (fun t : ℤ => (g t) ^ 2)) :
    Summable (fun t : ℤ => (f t - g t) ^ 2) := by
  have hpos : ∀ t : ℤ, 0 ≤ (f t - g t) ^ 2 := by intro t; exact sq_nonneg _
  have hle : ∀ t : ℤ, (f t - g t) ^ 2 ≤ 2 * (f t) ^ 2 + 2 * (g t) ^ 2 := by
    intro t
    exact sub_sq_le_two_sq (f t) (g t)
  have hsum2 : Summable (fun t : ℤ => 2 * (f t) ^ 2 + 2 * (g t) ^ 2) :=
    (summable_const_mul 2 hf2).add (summable_const_mul 2 hg2)
  exact Summable.of_nonneg_of_le hpos hle hsum2

/-- Finite subset mass of a nonnegative summable function is below its tsum. -/
lemma Finset_sum_le_tsum {f : ℤ → ℝ} (hfpos : ∀ t, 0 ≤ f t) (hf : Summable f)
    (E : Finset ℤ) : (∑ t ∈ E, f t) ≤ ∑' t : ℤ, f t := by
  have hgpos : ∀ t : ℤ, 0 ≤ (E : Set ℤ).indicator f t := by
    intro t
    by_cases ht : t ∈ (E : Set ℤ)
    · simpa [Set.indicator, ht] using hfpos t
    · simp [Set.indicator, ht]
  have hgle : ∀ t : ℤ, (E : Set ℤ).indicator f t ≤ f t := by
    intro t
    by_cases ht : t ∈ (E : Set ℤ)
    · simp [Set.indicator, ht]
    · simpa [Set.indicator, ht] using hfpos t
  have hsum_ind : Summable ((E : Set ℤ).indicator f) :=
    Summable.of_nonneg_of_le hgpos hgle hf
  calc
    (∑ t ∈ E, f t) = ∑' t : ℤ, (E : Set ℤ).indicator f t := by
      rw [tsum_eq_sum (s := E)]
      · apply Finset.sum_congr rfl
        intro t ht
        simp [Set.indicator, ht]
      · intro t ht
        have htnot : t ∉ (E : Set ℤ) := by simpa using ht
        simp [Set.indicator, htnot]
    _ ≤ ∑' t : ℤ, f t := Summable.tsum_le_tsum hgle hsum_ind hf

/-- Norm-level identity underlying the drop lemma. -/
lemma norm₂sq_mix_sub {p : ℝ} {f g : ℤ → ℝ}
    (hf2 : Summable (fun t : ℤ => (f t) ^ 2)) (hg2 : Summable (fun t : ℤ => (g t) ^ 2)) :
    norm₂sq (fun t : ℤ => (1 - p) * f t + p * g t) =
      (1 - p) * norm₂sq f + p * norm₂sq g - p * (1 - p) * norm₂sq (fun t : ℤ => f t - g t) := by
  let A : ℤ → ℝ := fun t => (1 - p) * (f t) ^ 2
  let B : ℤ → ℝ := fun t => p * (g t) ^ 2
  let C : ℤ → ℝ := fun t => p * (1 - p) * (f t - g t) ^ 2
  have hA : Summable A := by
    dsimp [A]
    exact summable_const_mul (1 - p) hf2
  have hB : Summable B := by
    dsimp [B]
    exact summable_const_mul p hg2
  have hC : Summable C := by
    dsimp [C]
    exact summable_const_mul (p * (1 - p)) (summable_sq_sub hf2 hg2)
  have hAB : Summable (fun t : ℤ => A t + B t) := hA.add hB
  have htsA : (∑' t : ℤ, A t) = (1 - p) * norm₂sq f := by
    dsimp [A, norm₂sq]
    rw [tsum_mul_left]
  have htsB : (∑' t : ℤ, B t) = p * norm₂sq g := by
    dsimp [B, norm₂sq]
    rw [tsum_mul_left]
  have htsC : (∑' t : ℤ, C t) = p * (1 - p) * norm₂sq (fun t : ℤ => f t - g t) := by
    dsimp [C, norm₂sq]
    rw [tsum_mul_left]
  have hpt : ∀ t : ℤ, ((1 - p) * f t + p * g t) ^ 2 = A t + B t - C t := by
    intro t
    dsimp [A, B, C]
    rw [sq_mix_eq]
  calc
    norm₂sq (fun t : ℤ => (1 - p) * f t + p * g t)
        = ∑' t : ℤ, ((1 - p) * f t + p * g t) ^ 2 := by rfl
    _ = ∑' t : ℤ, (A t + B t - C t) := by
          apply tsum_congr
          intro t
          exact hpt t
    _ = (∑' t : ℤ, (A t + B t)) - ∑' t : ℤ, C t := Summable.tsum_sub hAB hC
    _ = ((∑' t : ℤ, A t) + ∑' t : ℤ, B t) - ∑' t : ℤ, C t := by rw [Summable.tsum_add hA hB]
    _ = (1 - p) * norm₂sq f + p * norm₂sq g - p * (1 - p) * norm₂sq (fun t : ℤ => f t - g t) := by
          rw [htsA, htsB, htsC]

/-- The drop lemma (`Lemma l:aux -98745220985-32`): with `k ≤ E.card` and
`|f(t)−g(t)| ≥ κ` on `E`, the mixture norm drops by `p(1−p)κ²k`. -/
lemma l2_drop {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f g : ℤ → ℝ}
    (hf2 : Summable (fun t : ℤ => (f t) ^ 2)) (hg2 : Summable (fun t : ℤ => (g t) ^ 2))
    (E : Finset ℤ) {k : ℕ} (hk : k ≤ E.card) {κ : ℝ} (hκ : 0 ≤ κ)
    (hbig : ∀ t : ℤ, t ∈ E → κ ≤ |f t - g t|) :
    norm₂sq (fun t : ℤ => (1 - p) * f t + p * g t) ≤
      (1 - p) * norm₂sq f + p * norm₂sq g - p * (1 - p) * κ ^ 2 * (k : ℝ) := by
  have hfg : Summable (fun t : ℤ => (f t - g t) ^ 2) := summable_sq_sub hf2 hg2
  -- Σ_E (f−g)² ≥ κ²·|E|
  have hE_ge : κ ^ 2 * (E.card : ℝ) ≤ ∑ t ∈ E, (f t - g t) ^ 2 := by
    have hterm : ∀ t ∈ E, κ ^ 2 ≤ (f t - g t) ^ 2 := by
      intro t ht
      calc
        κ ^ 2 = |κ| ^ 2 := by rw [sq_abs]
        _ ≤ |f t - g t| ^ 2 := by
          exact sq_le_sq.mpr (by simpa [abs_of_nonneg hκ] using hbig t ht)
        _ = (f t - g t) ^ 2 := by rw [sq_abs]
    calc
      κ ^ 2 * (E.card : ℝ) = ∑ t ∈ E, κ ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ ∑ t ∈ E, (f t - g t) ^ 2 := Finset.sum_le_sum hterm
  have hE_tsum : (∑ t ∈ E, (f t - g t) ^ 2) ≤ norm₂sq (fun t : ℤ => f t - g t) := by
    exact Finset_sum_le_tsum (fun t => sq_nonneg _) hfg E
  have hkg : κ ^ 2 * (k : ℝ) ≤ norm₂sq (fun t : ℤ => f t - g t) := by
    calc
      κ ^ 2 * (k : ℝ) ≤ κ ^ 2 * (E.card : ℝ) := by
        apply mul_le_mul_of_nonneg_left
        · exact_mod_cast hk
        · exact sq_nonneg κ
      _ ≤ ∑ t ∈ E, (f t - g t) ^ 2 := hE_ge
      _ ≤ norm₂sq (fun t : ℤ => f t - g t) := hE_tsum
  have hpg : 0 ≤ p * (1 - p) := by
    have h1 : 0 ≤ 1 - p := by linarith
    exact mul_nonneg hp0 h1
  have hd : p * (1 - p) * κ ^ 2 * (k : ℝ) ≤ p * (1 - p) * norm₂sq (fun t : ℤ => f t - g t) := by
    have hsub : 0 ≤ norm₂sq (fun t : ℤ => f t - g t) - κ ^ 2 * (k : ℝ) := by linarith
    have hmul : 0 ≤ p * (1 - p) * (norm₂sq (fun t : ℤ => f t - g t) - κ ^ 2 * (k : ℝ)) := by
      exact mul_nonneg hpg hsub
    nlinarith
  calc
    norm₂sq (fun t : ℤ => (1 - p) * f t + p * g t)
        = (1 - p) * norm₂sq f + p * norm₂sq g - p * (1 - p) * norm₂sq (fun t : ℤ => f t - g t) :=
          norm₂sq_mix_sub hf2 hg2
    _ ≤ (1 - p) * norm₂sq f + p * norm₂sq g - p * (1 - p) * κ ^ 2 * (k : ℝ) := by nlinarith

/-- The drop lemma applied to `(1−p)g₁ + p·g₂(·+y)` (translation-invariant RHS). -/
lemma l2_drop_shift {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {g1 g2 : ℤ → ℝ}
    (hg1 : Summable (fun t : ℤ => (g1 t) ^ 2)) (hg2 : Summable (fun t : ℤ => (g2 t) ^ 2))
    (y : ℤ) (E : Finset ℤ) {k : ℕ} (hk : k ≤ E.card) {κ : ℝ} (hκ : 0 ≤ κ)
    (hbig : ∀ t : ℤ, t ∈ E → κ ≤ |g1 t - g2 (t + y)|) :
    norm₂sq (fun t : ℤ => (1 - p) * g1 t + p * g2 (t + y)) ≤
      (1 - p) * norm₂sq g1 + p * norm₂sq g2 - p * (1 - p) * κ ^ 2 * (k : ℝ) := by
  let G : ℤ → ℝ := fun t => g2 (t + y)
  have hG2 : Summable (fun t : ℤ => (G t) ^ 2) := by
    dsimp [G]
    exact summable_sq_translate_add y hg2
  have hdrop := l2_drop hp0 hp1 hg1 hG2 E hk hκ (by
    intro t ht
    dsimp [G]
    exact hbig t ht)
  have hnG2 : norm₂sq G = norm₂sq g2 := by
    dsimp [G]
    exact norm₂sq_translate_add (g := g2) y
  simpa [G, hnG2] using hdrop

end Submission.L2Norm
