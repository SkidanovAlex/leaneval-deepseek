import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Strict
import Submission.Work.Diff.Alg.Pinch.Chat
import Submission.Work.Diff.Alg.Pinch.ChatDefs
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.Alg.Pinch.inPIC2_cone_basic
import Submission.Work.Diff.Alg.Pinch.inPIC2_metric_basic
import Submission.Work.Diff.Alg.Pinch.ell_isAlgCurv
import Submission.Work.Diff.Alg.Pinch.ell_inv
import Submission.Work.Diff.Alg.PA.Defs
import Submission.Work.Diff.Alg.Pinch.Chat_quadform
import Submission.Work.Diff.Alg.Pinch.Chat_lagrange
import Submission.Work.Diff.Alg.Pinch.Chat_ric_margin
import Submission.Work.Diff.Alg.Pinch.Chat_linv_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The family `Ĉ(s)` exhausts the interior of the `PIC2` cone

Brendle–Schoen (Prop. 17, after Böhm–Wilking) build a pinching set containing a compact set `K` of
algebraic curvature tensors which are interior points of the cone `Ĉ = {InPIC2}` of nonnegative
complex sectional curvature.  The first step is that the whole compact set `K` sits inside one
member `Ĉ(s) = Chat n s` of the pinching family, for `s > 0` small enough:

`Chat_exhaust : K compact, K ⊂ int Ĉ  ⟹  ∃ s > 0, K ⊆ Ĉ(s)`.

## The mathematics

For `0 < s ≤ 1/2` the family is `Chat n s = ℓ_{a,s}(D(p))` with `a = chatA n s`, `p = chatP n s`
(`Chat_eq_Ccone`), where `D(p) = {R algebraic | InPIC2 R ∧ Ric ≥ p·scal/n}` and `ℓ_{a,b}` is the
Böhm–Wilking transform with explicit inverse `linv`.  Hence `R ∈ Chat n s` iff
`S = linv (chatA n s) s R` satisfies `IsAlgCurv S`, `InPIC2 S` and `RicPinch (chatP n s) S`.

As `s → 0⁺` we have `linv (chatA n s) s R = R + O(s)` (with `chatP n s = O(s²)`), so both conditions
follow from the *strict* hypotheses on `R`, provided the perturbation is smaller than the margin:

* `InPIC2`: for an **algebraic** curvature tensor `D` the quartic form `Cone.EF D` is a Hermitian
  form in the decomposable complex `2`-form `ζ ∧ η = (x+iy) ∧ (z+iw)`, hence dominated by
  `‖D‖ * EF (Iso n)`; this is the sharp form of "the round sphere lies in the interior of `Ĉ`
  *inside the subspace of algebraic tensors*" (`EF_algCurv_bound`), and it combines
  `Chat_quadform` (`4 EF D = ∑ Dᵢⱼₖₗ (qfAᵢⱼ qfAₖₗ + qfBᵢⱼ qfBₖₗ)`) and `Chat_lagrange`
  (`∑ (qfA² + qfB²) = 2 EF (Iso n)`) with Cauchy–Schwarz.  Then `InPIC2 (R - ε • Iso n)` gives
  `InPIC2 (R + D)` whenever `C ‖D‖ ≤ ε`, and the finitely many certificates `ε_R` on the compact
  set `K` can be made uniform.
* `RicPinch`: `InPIC2 (R - ε • Iso n)` gives `⟨Ric R v, v⟩ ≥ ε (n-1) ‖v‖²` (`Chat_ric_margin`),
  while `linv` perturbs `R` only by `O(s)·‖R‖` (`Chat_linv_bound`) and the `p`-term is `O(s²)`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Elementary bounds for the sup norm on `Curv4 n` -/

/-- Every component of `X : Curv4 n` is bounded by the (sup) norm of `X`. -/
lemma abs_component_le_norm (X : Curv4 n) (i j k l : Fin n) : |X i j k l| ≤ ‖X‖ := by
  have h1 := norm_le_pi_norm X i
  have h2 := norm_le_pi_norm (X i) j
  have h3 := norm_le_pi_norm (X i j) k
  have h4 := norm_le_pi_norm (X i j k) l
  simpa only [Real.norm_eq_abs] using le_trans h4 (le_trans h3 (le_trans h2 h1))

/-- Conversely, componentwise bounds give a bound on the norm. -/
lemma norm_le_of_components {X : Curv4 n} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j k l, |X i j k l| ≤ c) : ‖X‖ ≤ c := by
  rw [pi_norm_le_iff_of_nonneg hc]
  intro i
  rw [pi_norm_le_iff_of_nonneg hc]
  intro j
  rw [pi_norm_le_iff_of_nonneg hc]
  intro k
  rw [pi_norm_le_iff_of_nonneg hc]
  intro l
  rw [Real.norm_eq_abs]
  exact h i j k l

/-- `|scalAlg X| ≤ n^2 ‖X‖`. -/
lemma abs_scalAlg_le (X : Curv4 n) : |scalAlg X| ≤ (n : ℝ) ^ 2 * ‖X‖ := by
  have h1 : |scalAlg X| ≤ ∑ i, ∑ j, |X i j i j| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
  have h2 : ∑ i, ∑ j, |X i j i j| ≤ ∑ i, ∑ j, ‖X‖ :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => abs_component_le_norm X i j i j))
  have h3 : (∑ _i : Fin n, ∑ _j : Fin n, ‖X‖) = (n : ℝ) ^ 2 * ‖X‖ := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  linarith [h1, h2, h3]

/-- The `Ric`-quadratic form of a `4`-index array is bounded by `n^2 ‖X‖` times the Euclidean
square of `v`. -/
lemma abs_ricForm_le (X : Curv4 n) (v : Fin n → ℝ) :
    |∑ i, ∑ j, (∑ k, X k i k j) * v i * v j| ≤ (n : ℝ) ^ 2 * ‖X‖ * (∑ i, v i * v i) := by
  have hterm : ∀ i j, |(∑ k, X k i k j) * v i * v j| ≤ (n : ℝ) * ‖X‖ * (|v i| * |v j|) := by
    intro i j
    have h1 : |∑ k, X k i k j| ≤ (n : ℝ) * ‖X‖ := by
      calc |∑ k, X k i k j| ≤ ∑ k, |X k i k j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin n, ‖X‖ := Finset.sum_le_sum (fun k _ => abs_component_le_norm X k i k j)
        _ = (n : ℝ) * ‖X‖ := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc |(∑ k, X k i k j) * v i * v j|
        = |∑ k, X k i k j| * |v i| * |v j| := by rw [abs_mul, abs_mul]
      _ ≤ ((n : ℝ) * ‖X‖) * |v i| * |v j| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) (abs_nonneg _)
      _ = (n : ℝ) * ‖X‖ * (|v i| * |v j|) := by ring
  have hsum : (∑ i, ∑ j, (n : ℝ) * ‖X‖ * (|v i| * |v j|))
      = (n : ℝ) * ‖X‖ * ((∑ i, |v i|) * (∑ j, |v j|)) := by
    have hprod : (∑ i : Fin n, |v i|) * (∑ j : Fin n, |v j|)
        = ∑ i : Fin n, ∑ j : Fin n, |v i| * |v j| := Finset.sum_mul_sum _ _ _ _
    rw [hprod]
    simp only [Finset.mul_sum]
  have hsq : (∑ i, |v i|) * (∑ j, |v j|) ≤ (n : ℝ) * (∑ i, v i * v i) := by
    have h := sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) (fun i => |v i|)
      (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow] at h
    have hcard : (∑ _i : Fin n, (1 : ℝ)) = (n : ℝ) := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have habs : (∑ i, |v i| ^ 2) = ∑ i, v i * v i :=
      Finset.sum_congr rfl (fun i _ => by rw [sq_abs]; ring)
    rw [hcard, habs] at h
    have h3 : (∑ i, |v i|) ^ 2 = (∑ i, |v i|) * (∑ j, |v j|) := by
      rw [pow_two]
    rw [← h3]
    simpa only [mul_comm] using h
  calc |∑ i, ∑ j, (∑ k, X k i k j) * v i * v j|
      ≤ ∑ i, ∑ j, (n : ℝ) * ‖X‖ * (|v i| * |v j|) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        exact Finset.sum_le_sum (fun i _ =>
          le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun j _ => hterm i j)))
    _ = (n : ℝ) * ‖X‖ * ((∑ i, |v i|) * (∑ j, |v j|)) := hsum
    _ ≤ (n : ℝ) * ‖X‖ * ((n : ℝ) * (∑ i, v i * v i)) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (n : ℝ) ^ 2 * ‖X‖ * (∑ i, v i * v i) := by ring

/-! ## The round sphere is an interior point of the cone, inside the algebraic tensors -/

/-- `EF (Iso n) ≥ 0`, i.e. the round sphere lies in the cone. -/
theorem EF_Iso_nonneg (n : ℕ) (x y z w : Fin n → ℝ) : 0 ≤ Cone.EF (Iso n) x y z w :=
  (Cone.inPIC2_iff (Iso n)).mp (Cone.inPIC2_iso n) x y z w

/-- Abs-sum bound for a sum of products of the two halves of `D : Curv4 n`. -/
private lemma abs_sum_two_tensor (D : Curv4 n) (A B : Fin n → Fin n → ℝ) :
    |∑ i, ∑ j, ∑ k, ∑ l, D i j k l * (A i j * B k l)|
      ≤ ‖D‖ * (∑ i, ∑ j, |A i j|) * (∑ k, ∑ l, |B k l|) := by
  have hconv : (∑ i, ∑ j, ∑ k, ∑ l, D i j k l * (A i j * B k l))
      = ∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n,
          D p.1 p.2 q.1 q.2 * (A p.1 p.2 * B q.1 q.2) := by
    simp only [Fintype.sum_prod_type]
  have e1 : (∑ p : Fin n × Fin n, |A p.1 p.2|) = ∑ i, ∑ j, |A i j| := by
    rw [Fintype.sum_prod_type]
  have e2 : (∑ q : Fin n × Fin n, |B q.1 q.2|) = ∑ k, ∑ l, |B k l| := by
    rw [Fintype.sum_prod_type]
  have hprod : (∑ p : Fin n × Fin n, |A p.1 p.2|) * (∑ q : Fin n × Fin n, |B q.1 q.2|)
      = ∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, |A p.1 p.2| * |B q.1 q.2| :=
    Finset.sum_mul_sum _ _ _ _
  rw [hconv]
  have hstep : ∀ p q : Fin n × Fin n,
      |D p.1 p.2 q.1 q.2 * (A p.1 p.2 * B q.1 q.2)| ≤ ‖D‖ * (|A p.1 p.2| * |B q.1 q.2|) := by
    intro p q
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_component_le_norm D p.1 p.2 q.1 q.2)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  calc |∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n,
          D p.1 p.2 q.1 q.2 * (A p.1 p.2 * B q.1 q.2)|
      ≤ ∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, ‖D‖ * (|A p.1 p.2| * |B q.1 q.2|) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        refine Finset.sum_le_sum (fun p _ => ?_)
        exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun q _ => hstep p q))
    _ = ‖D‖ * (∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n,
          |A p.1 p.2| * |B q.1 q.2|) := by
        simp only [Finset.mul_sum]
    _ = ‖D‖ * (∑ i, ∑ j, |A i j|) * (∑ k, ∑ l, |B k l|) := by
        rw [← hprod, e1, e2]
        ring

/-- Cauchy–Schwarz: `(∑ᵢⱼ |Aᵢⱼ|)^2 ≤ n^2 ∑ᵢⱼ Aᵢⱼ²`. -/
private lemma sum_abs_sq_le (A : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, |A i j|) ^ 2 ≤ (n : ℝ) ^ 2 * (∑ i, ∑ j, A i j ^ 2) := by
  have e1 : (∑ p : Fin n × Fin n, |A p.1 p.2|) = ∑ i, ∑ j, |A i j| := by
    rw [Fintype.sum_prod_type]
  have e2 : (∑ p : Fin n × Fin n, |A p.1 p.2| ^ 2) = ∑ i, ∑ j, A i j ^ 2 := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [sq_abs]))
  have h := sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
    (fun p : Fin n × Fin n => |A p.1 p.2|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ] at h
  calc (∑ i, ∑ j, |A i j|) ^ 2 = (∑ p : Fin n × Fin n, |A p.1 p.2|) ^ 2 := by rw [e1]
    _ ≤ (∑ p : Fin n × Fin n, |A p.1 p.2| ^ 2) * (Fintype.card (Fin n × Fin n) • (1 : ℝ)) := h
    _ = (n : ℝ) ^ 2 * (∑ i, ∑ j, A i j ^ 2) := by
        rw [e2]
        simp only [Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, mul_one]
        ring

/-- **Key estimate.**  For an algebraic curvature tensor `D` the quartic form `EF D` — the real form
of `R(ζ,η,ζ̄,η̄)` — is bounded by `‖D‖` times the round-sphere form `EF (Iso n)`, which is the
squared norm of the decomposable `2`-form `ζ ∧ η`.  This is what makes `Iso n` an interior point of
the cone `{InPIC2}` *within the space of algebraic curvature tensors* (it is a boundary point of the
cone in the ambient space of all `4`-index arrays). -/
theorem EF_algCurv_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Curv4 n), IsAlgCurv D → ∀ x y z w : Fin n → ℝ,
      |Cone.EF D x y z w| ≤ C * ‖D‖ * Cone.EF (Iso n) x y z w := by
  refine ⟨(n : ℝ) ^ 2 + 1, by positivity, ?_⟩
  intro D hD x y z w
  set A : Fin n → Fin n → ℝ := qfA x y z w with hA
  set B : Fin n → Fin n → ℝ := qfB x y z w with hB
  have hq : 4 * Cone.EF D x y z w
      = ∑ i, ∑ j, ∑ k, ∑ l, D i j k l * (A i j * A k l + B i j * B k l) :=
    Chat_quadform hD x y z w
  have hl : (∑ i, ∑ j, (A i j ^ 2 + B i j ^ 2)) = 2 * Cone.EF (Iso n) x y z w :=
    Chat_lagrange n x y z w
  have hIso : 0 ≤ Cone.EF (Iso n) x y z w := EF_Iso_nonneg n x y z w
  have hsplit : (∑ i, ∑ j, ∑ k, ∑ l, D i j k l * (A i j * A k l + B i j * B k l))
      = (∑ i, ∑ j, ∑ k, ∑ l, D i j k l * (A i j * A k l))
        + (∑ i, ∑ j, ∑ k, ∑ l, D i j k l * (B i j * B k l)) := by
    simp only [mul_add, Finset.sum_add_distrib]
  have h1 := abs_sum_two_tensor D A A
  have h2 := abs_sum_two_tensor D B B
  have h1' : |∑ i, ∑ j, ∑ k, ∑ l, D i j k l * (A i j * A k l)|
      ≤ ‖D‖ * (∑ i, ∑ j, |A i j|) ^ 2 := by
    calc |∑ i, ∑ j, ∑ k, ∑ l, D i j k l * (A i j * A k l)|
        ≤ (‖D‖ * (∑ i, ∑ j, |A i j|)) * (∑ k, ∑ l, |A k l|) := h1
      _ = ‖D‖ * (∑ i, ∑ j, |A i j|) ^ 2 := by ring
  have h2' : |∑ i, ∑ j, ∑ k, ∑ l, D i j k l * (B i j * B k l)|
      ≤ ‖D‖ * (∑ i, ∑ j, |B i j|) ^ 2 := by
    calc |∑ i, ∑ j, ∑ k, ∑ l, D i j k l * (B i j * B k l)|
        ≤ (‖D‖ * (∑ i, ∑ j, |B i j|)) * (∑ k, ∑ l, |B k l|) := h2
      _ = ‖D‖ * (∑ i, ∑ j, |B i j|) ^ 2 := by ring
  have h3 := sum_abs_sq_le A
  have h4 := sum_abs_sq_le B
  have h5 : (∑ i, ∑ j, A i j ^ 2) + (∑ i, ∑ j, B i j ^ 2) = 2 * Cone.EF (Iso n) x y z w := by
    have hab : (∑ i, ∑ j, (A i j ^ 2 + B i j ^ 2))
        = (∑ i, ∑ j, A i j ^ 2) + (∑ i, ∑ j, B i j ^ 2) := by
      simp only [Finset.sum_add_distrib]
    rw [← hab, hl]
  have hDn : 0 ≤ ‖D‖ := norm_nonneg D
  -- the bound on the quadruple sum
  have hbound : |∑ i, ∑ j, ∑ k, ∑ l, D i j k l * (A i j * A k l + B i j * B k l)|
      ≤ ‖D‖ * (n : ℝ) ^ 2 * (2 * Cone.EF (Iso n) x y z w) := by
    rw [hsplit]
    refine le_trans (abs_add_le _ _) ?_
    have h34 : (∑ i, ∑ j, |A i j|) ^ 2 + (∑ i, ∑ j, |B i j|) ^ 2
        ≤ (n : ℝ) ^ 2 * ((∑ i, ∑ j, A i j ^ 2) + (∑ i, ∑ j, B i j ^ 2)) := by
      have hh := add_le_add h3 h4
      rwa [← mul_add] at hh
    calc |∑ i, ∑ j, ∑ k, ∑ l, D i j k l * (A i j * A k l)|
            + |∑ i, ∑ j, ∑ k, ∑ l, D i j k l * (B i j * B k l)|
        ≤ ‖D‖ * (∑ i, ∑ j, |A i j|) ^ 2 + ‖D‖ * (∑ i, ∑ j, |B i j|) ^ 2 := add_le_add h1' h2'
      _ = ‖D‖ * ((∑ i, ∑ j, |A i j|) ^ 2 + (∑ i, ∑ j, |B i j|) ^ 2) := by ring
      _ ≤ ‖D‖ * ((n : ℝ) ^ 2 * ((∑ i, ∑ j, A i j ^ 2) + (∑ i, ∑ j, B i j ^ 2))) :=
          mul_le_mul_of_nonneg_left h34 hDn
      _ = ‖D‖ * (n : ℝ) ^ 2 * (2 * Cone.EF (Iso n) x y z w) := by rw [h5]; ring
  have h4EF : (4 : ℝ) * |Cone.EF D x y z w| = |4 * Cone.EF D x y z w| := by
    rw [abs_mul]; norm_num
  have hmain : 4 * |Cone.EF D x y z w| ≤ 4 * (((n : ℝ) ^ 2 / 2) * ‖D‖ * Cone.EF (Iso n) x y z w) := by
    rw [h4EF, hq]
    calc |∑ i, ∑ j, ∑ k, ∑ l, D i j k l * (A i j * A k l + B i j * B k l)|
        ≤ ‖D‖ * (n : ℝ) ^ 2 * (2 * Cone.EF (Iso n) x y z w) := hbound
      _ = 4 * (((n : ℝ) ^ 2 / 2) * ‖D‖ * Cone.EF (Iso n) x y z w) := by ring
  have hkey : |Cone.EF D x y z w| ≤ ((n : ℝ) ^ 2 / 2) * ‖D‖ * Cone.EF (Iso n) x y z w := by
    linarith [hmain]
  calc |Cone.EF D x y z w| ≤ ((n : ℝ) ^ 2 / 2) * ‖D‖ * Cone.EF (Iso n) x y z w := hkey
    _ ≤ ((n : ℝ) ^ 2 + 1) * ‖D‖ * Cone.EF (Iso n) x y z w := by
        have h1 : ((n : ℝ) ^ 2 / 2) ≤ (n : ℝ) ^ 2 + 1 := by nlinarith [sq_nonneg (n : ℝ)]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hDn) hIso

/-! ## `linv` preserves algebraic curvature tensors -/

lemma isAlgCurv_sub' {R S : Curv4 n} (hR : IsAlgCurv R) (hS : IsAlgCurv S) :
    IsAlgCurv (R - S) := by
  have h : IsAlgCurv (R + (-1 : ℝ) • S) := isAlgCurv_add hR (isAlgCurv_smul (-1) hS)
  have hEq : R + (-1 : ℝ) • S = R - S := by
    ext i j k l
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    ring
  rwa [hEq] at h

lemma linv_isAlgCurv {a b : ℝ} {R : Curv4 n} (hR : IsAlgCurv R) : IsAlgCurv (linv a b R) := by
  have h1 : IsAlgCurv (knProd (ric0 R) (id2 n)) :=
    knProd_isAlgCurv (fun i j => ric0_symm hR i j) (fun i j => id2_symm i j)
  have h2 : IsAlgCurv (knProd (id2 n) (id2 n)) :=
    knProd_isAlgCurv (fun i j => id2_symm i j) (fun i j => id2_symm i j)
  rw [linv]
  exact isAlgCurv_sub' (isAlgCurv_sub' hR (isAlgCurv_smul _ h1)) (isAlgCurv_smul _ h2)

lemma sq_le_half {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) : s ^ 2 ≤ s / 2 := by
  nlinarith [sq_nonneg (s - 1 / 2)]

/-! ## The exhaustion theorem -/

theorem Chat_exhaust (n : ℕ) (hn : 2 ≤ n) :
    ∀ K : Set (Submission.Diff.Alg.Curv4 n), IsCompact K →
      (∀ R ∈ K, Submission.Diff.Alg.IsAlgCurv R ∧
        ∃ ε : ℝ, 0 < ε ∧ Submission.Diff.Alg.InPIC2 (R - ε • Submission.Diff.Alg.Iso n)) →
      ∃ s : ℝ, 0 < s ∧ ∀ R ∈ K, R ∈ Work.Diff.Alg.Pinch.Chat n s := by
  obtain ⟨C, hCpos, hC⟩ := EF_algCurv_bound n
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hnc : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  intro K hKc hK
  classical
  -- certificates
  let γ : Curv4 n → ℝ := fun R =>
    if h : ∃ ε : ℝ, 0 < ε ∧ InPIC2 (R - ε • Iso n) then Classical.choose h else 1
  have hγspec : ∀ R ∈ K, 0 < γ R ∧ InPIC2 (R - γ R • Iso n) := by
    intro R hR
    have hex := (hK R hR).2
    dsimp only [γ]
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  -- uniform margin on the compact set
  have hmargin : ∃ ε : ℝ, 0 < ε ∧ ∀ R ∈ K, InPIC2 (R - ε • Iso n) := by
    rcases Set.eq_empty_or_nonempty K with hem | hne
    · refine ⟨1, one_pos, ?_⟩
      intro R hR
      rw [hem] at hR
      exact absurd hR (Set.notMem_empty R)
    · have hcover : K ⊆ ⋃ j : {R // R ∈ K}, Metric.ball (j : Curv4 n) (γ j / (2 * C)) := by
        intro R hR
        rw [Set.mem_iUnion]
        refine ⟨⟨R, hR⟩, ?_⟩
        rw [Metric.mem_ball, dist_self]
        have := (hγspec R hR).1
        positivity
      obtain ⟨t, ht⟩ := hKc.elim_finite_subcover
        (fun j : {R // R ∈ K} => Metric.ball (j : Curv4 n) (γ j / (2 * C)))
        (fun _ => Metric.isOpen_ball) hcover
      have htne : t.Nonempty := by
        rcases Finset.eq_empty_or_nonempty t with h | h
        · exfalso
          obtain ⟨R, hR⟩ := hne
          have hmem := ht hR
          rw [h] at hmem
          simp at hmem
        · exact h
      let g : {R // R ∈ K} → ℝ := fun j => γ (j : Curv4 n) / 2
      refine ⟨t.inf' htne g, ?_, ?_⟩
      · rw [Finset.lt_inf'_iff]
        intro j _
        exact half_pos (hγspec (j : Curv4 n) j.2).1
      · intro R hR
        have hmem := ht hR
        simp only [Set.mem_iUnion] at hmem
        obtain ⟨j, hj, hjball⟩ := hmem
        have hdist : ‖R - (j : Curv4 n)‖ < γ (j : Curv4 n) / (2 * C) := by
          rw [Metric.mem_ball, dist_eq_norm] at hjball
          exact hjball
        have hεle : t.inf' htne g ≤ g j := Finset.inf'_le g hj
        have hgval : g j = γ (j : Curv4 n) / 2 := rfl
        have hRalg : ∀ Q : Curv4 n, Q ∈ K → IsAlgCurv Q := fun Q hQ => (hK Q hQ).1
        have hsub : IsAlgCurv (R - (j : Curv4 n)) :=
          isAlgCurv_sub' (hRalg R hR) (hRalg (j : Curv4 n) j.2)
        have hB : C * ‖R - (j : Curv4 n)‖ ≤ γ (j : Curv4 n) / 2 := by
          have hcancel : C * (γ (j : Curv4 n) / (2 * C)) = γ (j : Curv4 n) / 2 := by field_simp
          rw [← hcancel]
          exact mul_le_mul_of_nonneg_left hdist.le hCpos.le
        have hIso := EF_Iso_nonneg n
        intro x y z w
        change 0 ≤ Cone.EF (R - t.inf' htne g • Iso n) x y z w
        have hdecomp : R - t.inf' htne g • Iso n
            = ((j : Curv4 n) - γ (j : Curv4 n) • Iso n)
              + ((R - (j : Curv4 n)) + (γ (j : Curv4 n) - t.inf' htne g) • Iso n) := by
          ext a b c d
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
          ring
        rw [hdecomp, Cone.EF_add, Cone.EF_add, Cone.EF_smul]
        have hA : 0 ≤ Cone.EF ((j : Curv4 n) - γ (j : Curv4 n) • Iso n) x y z w :=
          (Cone.inPIC2_iff _).mp (hγspec (j : Curv4 n) j.2).2 x y z w
        have hD0 : 0 ≤ Cone.EF (Iso n) x y z w := hIso x y z w
        have hb : -((C * ‖R - (j : Curv4 n)‖) * Cone.EF (Iso n) x y z w)
            ≤ Cone.EF (R - (j : Curv4 n)) x y z w := by
          have h := (abs_le.mp (hC (R - (j : Curv4 n)) hsub x y z w)).1
          linarith [h]
        have hle2 : 0 ≤ γ (j : Curv4 n) - t.inf' htne g := by
          have hγpos' : 0 ≤ γ (j : Curv4 n) := (hγspec (j : Curv4 n) j.2).1.le
          rw [hgval] at hεle
          linarith
        have hkey : C * ‖R - (j : Curv4 n)‖ ≤ γ (j : Curv4 n) - t.inf' htne g := by
          linarith
        have hmul := mul_le_mul_of_nonneg_right hkey hD0
        linarith
  obtain ⟨ε, hεpos, hεK⟩ := hmargin
  -- boundedness of `K`
  obtain ⟨M₀, hM₀⟩ := hKc.isBounded.exists_norm_le
  let M : ℝ := max M₀ 1
  have hMpos : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hMb : ∀ R ∈ K, ‖R‖ ≤ M := fun R hR => le_trans (hM₀ R hR) (le_max_left _ _)
  -- constants
  let K₁ : ℝ := 8 * (n : ℝ) ^ 2 + 16
  have hK₁pos : 0 < K₁ := by dsimp only [K₁]; positivity
  let D₀ : ℝ := (n : ℝ) ^ 2 * K₁ * M + (n : ℝ) * ((n : ℝ) - 2) * M * (1 + K₁) / 2
  have hD₀pos : 0 < D₀ := by
    dsimp only [D₀]
    have h1 : 0 < (n : ℝ) ^ 2 * K₁ * M := by positivity
    have h2 : 0 ≤ (n : ℝ) * ((n : ℝ) - 2) * M * (1 + K₁) / 2 := by
      have h3 : (0 : ℝ) ≤ 1 + K₁ := by linarith
      positivity
    linarith
  refine ⟨min (1 / 2) (min (ε / (2 * C * K₁ * M)) (ε * ((n : ℝ) - 1) / D₀)),
    lt_min (by norm_num) (lt_min (by positivity) (by positivity)), ?_⟩
  intro R hR
  set s : ℝ := min (1 / 2) (min (ε / (2 * C * K₁ * M)) (ε * ((n : ℝ) - 1) / D₀)) with hsdef
  have hspos : 0 < s := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hs12 : s ≤ 1 / 2 := min_le_left _ _
  have hsC : s ≤ ε / (2 * C * K₁ * M) := le_trans (min_le_right _ _) (min_le_left _ _)
  have hsD : s ≤ ε * ((n : ℝ) - 1) / D₀ := le_trans (min_le_right _ _) (min_le_right _ _)
  have hRalg : IsAlgCurv R := (hK R hR).1
  -- the candidate preimage
  set S : Curv4 n := linv (chatA n s) s R with hSdef
  have hS_alg : IsAlgCurv S := linv_isAlgCurv hRalg
  -- `linv` is `O(s)`-close to the identity
  have hSRcomp : ∀ i j k l, |(S - R) i j k l| ≤ K₁ * s * ‖R‖ := by
    intro i j k l
    have h := Chat_linv_bound hn hspos hs12 R i j k l
    rw [hSdef, show K₁ = 8 * (n : ℝ) ^ 2 + 16 from rfl]
    exact h
  have hSRnorm : ‖S - R‖ ≤ K₁ * s * M := by
    refine norm_le_of_components (by positivity) (fun i j k l => ?_)
    exact le_trans (hSRcomp i j k l)
      (mul_le_mul_of_nonneg_left (hMb R hR) (by positivity))
  have hSRC : C * ‖S - R‖ ≤ ε / 2 := by
    have h1 : K₁ * s * M ≤ ε / (2 * C) := by
      have hden : 0 < 2 * C * K₁ * M := by positivity
      have h2 : s * (2 * C * K₁ * M) ≤ ε := by
        have h := mul_le_mul_of_nonneg_right hsC hden.le
        rwa [div_mul_cancel₀ ε (ne_of_gt hden)] at h
      have h3 : (K₁ * s * M) * (2 * C) ≤ ε := by
        rw [show (K₁ * s * M) * (2 * C) = s * (2 * C * K₁ * M) from by ring]
        exact h2
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * C)]
      exact h3
    calc C * ‖S - R‖ ≤ C * (K₁ * s * M) := mul_le_mul_of_nonneg_left hSRnorm hCpos.le
      _ ≤ C * (ε / (2 * C)) := mul_le_mul_of_nonneg_left h1 hCpos.le
      _ = ε / 2 := by field_simp
  -- `InPIC2 S`
  have hPIC : InPIC2 S := by
    intro x y z w
    change 0 ≤ Cone.EF S x y z w
    have hdecomp : S = (R - ε • Iso n) + (ε • Iso n + (S - R)) := by
      ext i j k l
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      ring
    rw [hdecomp, Cone.EF_add, Cone.EF_add, Cone.EF_smul]
    have h1 : 0 ≤ Cone.EF (R - ε • Iso n) x y z w := hεK R hR x y z w
    have h2 : -((C * ‖S - R‖) * Cone.EF (Iso n) x y z w) ≤ Cone.EF (S - R) x y z w := by
      have h := (abs_le.mp (hC (S - R) (isAlgCurv_sub' hS_alg hRalg) x y z w)).1
      linarith [h]
    have h3 : 0 ≤ Cone.EF (Iso n) x y z w := EF_Iso_nonneg n x y z w
    have hmul := mul_le_mul_of_nonneg_right hSRC h3
    nlinarith [h1, h2, h3, hmul]
  -- `RicPinch p S`
  have hRic : RicPinch (chatP n s) S := by
    intro v
    change (chatP n s * scalAlg S / (n : ℝ)) * (∑ i, v i * v i)
      ≤ ∑ i, ∑ j, (∑ k, S k i k j) * v i * v j
    have hQ0 : 0 ≤ ∑ i, v i * v i := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    have hsplit : (∑ i, ∑ j, (∑ k, S k i k j) * v i * v j)
        = (∑ i, ∑ j, (∑ k, R k i k j) * v i * v j)
          + (∑ i, ∑ j, (∑ k, (S - R) k i k j) * v i * v j) := by
      have hpoint : ∀ i j, (∑ k, S k i k j) * v i * v j
          = (∑ k, R k i k j) * v i * v j + (∑ k, (S - R) k i k j) * v i * v j := by
        intro i j
        have hk : (∑ k, S k i k j) = (∑ k, R k i k j) + (∑ k, (S - R) k i k j) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun k _ => by simp only [Pi.sub_apply]; ring)
        rw [hk]; ring
      simp only [hpoint, Finset.sum_add_distrib]
    have hm := Chat_ric_margin hεpos (hεK R hR) v
    have hQD : -((n : ℝ) ^ 2 * ‖S - R‖ * (∑ i, v i * v i))
        ≤ (∑ i, ∑ j, (∑ k, (S - R) k i k j) * v i * v j) :=
      neg_le_of_abs_le (abs_ricForm_le (S - R) v)
    have hp0 : 0 ≤ chatP n s := chatP_nonneg hn s
    have hscal := abs_scalAlg_le S
    have hpS : (chatP n s * scalAlg S / (n : ℝ)) * (∑ i, v i * v i)
        ≤ (n : ℝ) * chatP n s * ‖S‖ * (∑ i, v i * v i) := by
      have hnn : 0 ≤ chatP n s / (n : ℝ) := div_nonneg hp0 hnpos.le
      have h1 : chatP n s * scalAlg S / (n : ℝ) ≤ (n : ℝ) * chatP n s * ‖S‖ := by
        have hle : scalAlg S ≤ |scalAlg S| := le_abs_self _
        calc chatP n s * scalAlg S / (n : ℝ) = (chatP n s / (n : ℝ)) * scalAlg S := by ring
          _ ≤ (chatP n s / (n : ℝ)) * |scalAlg S| := mul_le_mul_of_nonneg_left hle hnn
          _ ≤ (chatP n s / (n : ℝ)) * ((n : ℝ) ^ 2 * ‖S‖) := mul_le_mul_of_nonneg_left hscal hnn
          _ = (n : ℝ) * chatP n s * ‖S‖ := by field_simp
      exact mul_le_mul_of_nonneg_right h1 hQ0
    have hSnorm : ‖S‖ ≤ M * (1 + K₁) := by
      have h1 : ‖S‖ ≤ ‖R‖ + ‖S - R‖ := by
        calc ‖S‖ = ‖R + (S - R)‖ := by rw [add_sub_cancel]
          _ ≤ ‖R‖ + ‖S - R‖ := norm_add_le _ _
      have h2 : K₁ * s * M ≤ K₁ * M := by
        have h2a : K₁ * s ≤ K₁ := by
          have hh := mul_le_mul_of_nonneg_left hs12 hK₁pos.le
          linarith [hh, hK₁pos]
        exact mul_le_mul_of_nonneg_right h2a hMpos.le
      linarith [h1, hSRnorm, h2, hMb R hR]
    have hp_le : chatP n s ≤ ((n : ℝ) - 2) * s ^ 2 := chatP_le hn hspos.le
    have hsqhalf : s ^ 2 ≤ s / 2 := sq_le_half hspos.le hs12
    have hkey : (n : ℝ) ^ 2 * ‖S - R‖ + (n : ℝ) * chatP n s * ‖S‖ ≤ ε * ((n : ℝ) - 1) := by
      have h1 : (n : ℝ) ^ 2 * ‖S - R‖ ≤ (n : ℝ) ^ 2 * (K₁ * s * M) :=
        mul_le_mul_of_nonneg_left hSRnorm (by positivity)
      have h2 : (n : ℝ) * chatP n s * ‖S‖
          ≤ (n : ℝ) * (((n : ℝ) - 2) * s ^ 2) * (M * (1 + K₁)) := by
        have h2b : chatP n s * ‖S‖ ≤ (((n : ℝ) - 2) * s ^ 2) * (M * (1 + K₁)) :=
          mul_le_mul hp_le hSnorm (norm_nonneg _) (by positivity)
        calc (n : ℝ) * chatP n s * ‖S‖ = (n : ℝ) * (chatP n s * ‖S‖) := by ring
          _ ≤ (n : ℝ) * ((((n : ℝ) - 2) * s ^ 2) * (M * (1 + K₁))) :=
              mul_le_mul_of_nonneg_left h2b hnpos.le
          _ = (n : ℝ) * (((n : ℝ) - 2) * s ^ 2) * (M * (1 + K₁)) := by ring
      have h3 : (n : ℝ) * (((n : ℝ) - 2) * s ^ 2) * (M * (1 + K₁))
          ≤ s * ((n : ℝ) * ((n : ℝ) - 2) * M * (1 + K₁) / 2) := by
        have h2b : ((n : ℝ) - 2) * s ^ 2 ≤ ((n : ℝ) - 2) * (s / 2) :=
          mul_le_mul_of_nonneg_left hsqhalf hnc
        calc (n : ℝ) * (((n : ℝ) - 2) * s ^ 2) * (M * (1 + K₁))
            ≤ (n : ℝ) * (((n : ℝ) - 2) * (s / 2)) * (M * (1 + K₁)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2b hnpos.le) (by positivity)
          _ = s * ((n : ℝ) * ((n : ℝ) - 2) * M * (1 + K₁) / 2) := by ring
      have h4 : (n : ℝ) ^ 2 * (K₁ * s * M) = s * ((n : ℝ) ^ 2 * K₁ * M) := by ring
      have h5 : s * ((n : ℝ) ^ 2 * K₁ * M) + s * ((n : ℝ) * ((n : ℝ) - 2) * M * (1 + K₁) / 2)
          ≤ ε * ((n : ℝ) - 1) := by
        have heq : s * ((n : ℝ) ^ 2 * K₁ * M)
            + s * ((n : ℝ) * ((n : ℝ) - 2) * M * (1 + K₁) / 2) = s * D₀ := by
          dsimp only [D₀]; ring
        rw [heq]
        have h := mul_le_mul_of_nonneg_right hsD hD₀pos.le
        rwa [div_mul_cancel₀ (ε * ((n : ℝ) - 1)) (ne_of_gt hD₀pos)] at h
      linarith [h1, h2, h3, h4.le, h4.ge, h5]
    have hcomb : (n : ℝ) * chatP n s * ‖S‖ * (∑ i, v i * v i)
        ≤ ε * ((n : ℝ) - 1) * (∑ i, v i * v i)
          - (n : ℝ) ^ 2 * ‖S - R‖ * (∑ i, v i * v i) := by
      have hmul := mul_le_mul_of_nonneg_right hkey hQ0
      have he : ((n : ℝ) ^ 2 * ‖S - R‖ + (n : ℝ) * chatP n s * ‖S‖) * (∑ i, v i * v i)
          = (n : ℝ) ^ 2 * ‖S - R‖ * (∑ i, v i * v i)
            + (n : ℝ) * chatP n s * ‖S‖ * (∑ i, v i * v i) := by ring
      linarith [hmul, he.le, he.ge]
    rw [hsplit]
    linarith [hm, hQD, hpS, hcomb]
  -- the Böhm–Wilking transform inverts `linv`
  have ha0 : 0 ≤ chatA n s := chatA_nonneg hn hspos.le
  have hden1 : 1 + 2 * ((n : ℝ) - 1) * chatA n s ≠ 0 := by nlinarith [ha0, hn1]
  have hden2 : 1 + ((n : ℝ) - 2) * s ≠ 0 := by nlinarith [hnc, hspos]
  have hell : ell (chatA n s) s S = R := by
    rw [hSdef]
    exact ell_linv n hden1 hden2 hRalg
  rw [Chat_eq_Ccone n hs12]
  exact ⟨S, ⟨hS_alg, hPIC, hRic⟩, hell⟩

end Work.Diff.Alg.Pinch
