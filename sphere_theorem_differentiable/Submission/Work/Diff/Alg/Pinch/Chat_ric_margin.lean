import Mathlib
import Submission.Work.Diff.Alg.Pinch.ChatDefs
import Submission.Work.Diff.Alg.Pinch.inPIC2_metric_basic
import Submission.Work.Diff.Alg.Pinch.inPIC2_cone_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- Linearity of `R4` in the tensor argument, in the form used below: subtracting a multiple of
another tensor. -/
lemma R4_sub_smul (R S : Curv4 n) (t : ℝ) (a b c d : Fin n → ℝ) :
    R4 (R - t • S) a b c d = R4 R a b c d - t * R4 S a b c d := by
  have h : R - t • S = R + (-t) • S := by
    ext i j k l
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, Cone.R4_add_tensor, Cone.R4_smul_tensor]
  ring

/-- `dot (eₖ) v = vₖ` for the standard basis vector `eₖ = Pi.single k 1`. -/
lemma dot_single_left (v : Fin n → ℝ) (k : Fin n) : dot (Pi.single k 1) v = v k := by
  rw [dot, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- `dot v (eₖ) = vₖ` for the standard basis vector `eₖ = Pi.single k 1`. -/
lemma dot_single_right (v : Fin n → ℝ) (k : Fin n) : dot v (Pi.single k 1) = v k := by
  rw [dot, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- The standard basis vector has unit length. -/
lemma dot_single_single (k : Fin n) : dot (Pi.single k 1) (Pi.single k 1) = 1 := by
  rw [dot_single_left]
  simp

/-- `R4 (Iso n) eₖ v eₖ v = ‖v‖² - vₖ²`. -/
lemma r4_iso_single (v : Fin n → ℝ) (k : Fin n) :
    R4 (Iso n) (Pi.single k 1) v (Pi.single k 1) v = (∑ i, v i * v i) - v k * v k := by
  rw [Cone.r4_iso n (Pi.single k 1) v (Pi.single k 1) v,
    dot_single_single, dot_single_left, dot_single_right]
  simp only [dot, one_mul]

/-- A quantitative form of the fact that `InPIC2` controls the Ricci form: if `R - ε • Iso n` has nonnegative complex sectional curvature (`InPIC2`), then the Ricci quadratic form of `R` dominates `ε (n-1) ‖v‖²`:

`⟨Ric(R) v, v⟩ = ∑ᵢⱼ (∑ₖ R k i k j) vᵢ vⱼ ≥ ε (n-1) ∑ᵢ vᵢ²`.

Route: `InPIC2 D` implies `0 ≤ R4 D x z x z` for all `x z` (see `inPIC2_R4_nonneg`, `Diff/Alg/Pinch/inPIC2_metric_basic`); applied with `D = R - ε • Iso n` and `x = z = eₖ` (standard basis vector `Pi.single k 1`) this yields `R4 R eₖ v eₖ v ≥ ε * R4 (Iso n) eₖ v eₖ v = ε * (∑ᵢ vᵢ² - vₖ²)`, because `R4` is linear in the tensor argument (`R4_add_tensor`, `R4_smul_tensor` in `Diff/Alg/Pinch/inPIC2_cone_basic`) while `R4 (Iso n) eₖ v eₖ v = dot eₖ eₖ * dot v v - dot eₖ v * dot v eₖ` (`r4_iso`).  Summing these inequalities over `k` and using `ricForm_eq : ∑ᵢⱼ (∑ₖ R k i k j) vᵢ vⱼ = ∑ₖ R4 R eₖ v eₖ v` (`Diff/Alg/Pinch/inPIC2_metric_basic`) gives the claim.  Note `hε` is not really needed (linearity of `R4` in the tensor gives the inequality for every real `ε`), but it is kept for readability. -/
theorem Chat_ric_margin {n : ℕ} {R : Submission.Diff.Alg.Curv4 n} {ε : ℝ} (hε : 0 < ε)
    (hR : Submission.Diff.Alg.InPIC2 (R - ε • Submission.Diff.Alg.Iso n)) (v : Fin n → ℝ) :
    ε * ((n : ℝ) - 1) * (∑ i, v i * v i)
      ≤ ∑ i, ∑ j, (∑ k, R k i k j) * v i * v j := by
  have _ : (0 : ℝ) < ε := hε
  -- Pointwise inequality, one basis vector `eₖ` at a time.
  have key : ∀ k : Fin n, ε * ((∑ i, v i * v i) - v k * v k)
      ≤ R4 R (Pi.single k 1) v (Pi.single k 1) v := by
    intro k
    have h := inPIC2_R4_nonneg (R - ε • Iso n) hR (Pi.single k 1) v
    rw [R4_sub_smul, r4_iso_single] at h
    linarith
  -- Summing the pointwise inequalities over `k`.
  have hsum : (∑ k : Fin n, ε * ((∑ i, v i * v i) - v k * v k))
      = ε * ((n : ℝ) - 1) * (∑ i, v i * v i) := by
    rw [← Finset.mul_sum]
    have h1 : (∑ k : Fin n, ((∑ i, v i * v i) - v k * v k))
        = (n : ℝ) * (∑ i, v i * v i) - (∑ i, v i * v i) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    rw [h1]; ring
  calc ε * ((n : ℝ) - 1) * (∑ i, v i * v i)
      = ∑ k : Fin n, ε * ((∑ i, v i * v i) - v k * v k) := hsum.symm
    _ ≤ ∑ k : Fin n, R4 R (Pi.single k 1) v (Pi.single k 1) v :=
        Finset.sum_le_sum (fun k _ => key k)
    _ = ∑ i, ∑ j, (∑ k, R k i k j) * v i * v j := (ricForm_eq R v).symm

end Work.Diff.Alg.Pinch
