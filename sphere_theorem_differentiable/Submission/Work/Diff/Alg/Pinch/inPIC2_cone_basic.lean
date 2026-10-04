import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `InPIC2` is a closed convex cone

Closure properties of the cone `Submission.Diff.Alg.InPIC2` of algebraic curvature tensors with
nonnegative complex sectional curvature (Brendle–Schoen's cone `Ĉ`).

The condition `InPIC2 R` is `0 ≤ EF R x y z w` for all vectors `x y z w`, where `EF` is the real
quartic form of Brendle–Schoen.  The form `EF` is *linear* in the tensor variable `R`, so the
level set `InPIC2` is a closed convex cone; the remaining contents are that it contains the round
sphere `Iso n` (Cauchy–Schwarz for the hermitian pairing: the round sphere has nonnegative
isotropic curvature) and that it is invariant under a change of frame `rot A` (`A ∈ O(n)`, in fact
any matrix, by the frame-transport identity `R4 (rot A R) x y z w = R4 R (Aᵀx) (Aᵀy) (Aᵀz) (Aᵀw)`).
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

namespace Cone

/-! ## The quartic form defining `InPIC2` -/

/-- The quartic form `R(x,z,x,z) + R(x,w,x,w) + R(y,z,y,z) + R(y,w,y,w) - 2 R(x,y,z,w)`; its
nonnegativity for all `x y z w` is `InPIC2`.  It is linear in the tensor variable `R`. -/
noncomputable def EF (R : Curv4 n) (x y z w : Fin n → ℝ) : ℝ :=
  R4 R x z x z + R4 R x w x w + R4 R y z y z + R4 R y w y w - 2 * R4 R x y z w

theorem inPIC2_iff (R : Curv4 n) : InPIC2 R ↔ ∀ x y z w, 0 ≤ EF R x y z w := Iff.rfl

/-! ## Elementary sum lemmas

The proofs below reduce the identities to finite sums over `Fin n`; these are the generic
reindexing/expansion lemmas they use. -/

/-- Picking out one term of a sum against a Kronecker delta. -/
theorem sum_ite_delta (E : Fin n → ℝ) (j : Fin n) :
    (∑ l, (if j = l then (1:ℝ) else 0) * E l) = E j := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [show ¬ (j = b) from fun h => hb h.symm]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- Two Kronecker deltas contract a double sum against a product of two sequences. -/
theorem delta_pair (E F : Fin n → ℝ) (i j : Fin n) :
    (∑ k, ∑ l, ((if i = k then (1:ℝ) else 0) * (if j = l then 1 else 0)) * (E k * F l))
      = E i * F j := by
  have step : ∀ k, (∑ l, ((if i = k then (1:ℝ) else 0) * (if j = l then 1 else 0)) * (E k * F l))
      = ((if i = k then (1:ℝ) else 0) * E k) * F j := by
    intro k
    have h : ∀ l, ((if i = k then (1:ℝ) else 0) * (if j = l then 1 else 0)) * (E k * F l)
        = ((if i = k then (1:ℝ) else 0) * E k) * ((if j = l then 1 else 0) * F l) := fun l => by ring
    rw [Finset.sum_congr rfl (fun l _ => h l), ← Finset.mul_sum, sum_ite_delta F j]
  rw [Finset.sum_congr rfl (fun k _ => step k), ← Finset.sum_mul, sum_ite_delta E i]

/-- Cauchy–Schwarz in `ℂⁿ`, in real coordinates: if `u i ^ 2 + v i ^ 2 = a i * b i` then
`(∑ u) ^ 2 + (∑ v) ^ 2 ≤ (∑ a) * (∑ b)`. -/
theorem pair_cs (u v a b : Fin n → ℝ) (h : ∀ i, u i ^ 2 + v i ^ 2 = a i * b i)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (∑ i, u i) ^ 2 + (∑ i, v i) ^ 2 ≤ (∑ i, a i) * (∑ i, b i) := by
  have hsum : (∑ i, u i) ^ 2 + (∑ i, v i) ^ 2
      = Complex.normSq (∑ i, ((u i : ℂ) + (v i : ℂ) * Complex.I)) := by
    rw [Complex.normSq_apply, Complex.re_sum, Complex.im_sum]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring_nf
  have hζnorm : ∀ i, ‖((u i : ℂ) + (v i : ℂ) * Complex.I)‖ = Real.sqrt (a i) * Real.sqrt (b i) := by
    intro i
    have h1 : Complex.normSq ((u i : ℂ) + (v i : ℂ) * Complex.I) = a i * b i := by
      rw [Complex.normSq_add_mul_I, h i]
    have h2 : ‖((u i : ℂ) + (v i : ℂ) * Complex.I)‖ = Real.sqrt (a i * b i) := by
      rw [← Real.sqrt_sq (norm_nonneg _), ← Complex.normSq_eq_norm_sq, h1]
    rw [h2, Real.sqrt_mul (ha i) (b i)]
  have hcs : (∑ i, Real.sqrt (a i) * Real.sqrt (b i)) ^ 2 ≤ (∑ i, a i) * (∑ i, b i) := by
    have h1 : (∑ i, (Real.sqrt (a i)) ^ 2) = ∑ i, a i :=
      Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (ha i))
    have h2 : (∑ i, (Real.sqrt (b i)) ^ 2) = ∑ i, b i :=
      Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hb i))
    have h3 := sum_mul_sq_le_sq_mul_sq (Finset.univ) (fun i => Real.sqrt (a i))
      (fun i => Real.sqrt (b i))
    rw [h1, h2] at h3
    exact h3
  rw [hsum, Complex.normSq_eq_norm_sq]
  calc ‖∑ i, ((u i : ℂ) + (v i : ℂ) * Complex.I)‖ ^ 2
      ≤ (∑ i, ‖((u i : ℂ) + (v i : ℂ) * Complex.I)‖) ^ 2 := by
        have h := norm_sum_le (Finset.univ) (fun i => ((u i : ℂ) + (v i : ℂ) * Complex.I))
        exact pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = (∑ i, Real.sqrt (a i) * Real.sqrt (b i)) ^ 2 := by
        congr 1
        exact Finset.sum_congr rfl (fun i _ => hζnorm i)
    _ ≤ _ := hcs

theorem dot_comm (u v : Fin n → ℝ) : dot u v = dot v u := by
  simp only [dot]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem sums2_mul (F : Fin n → Fin n → ℝ) (G : Fin n → ℝ) :
    (∑ a, ∑ b, F a b) * (∑ c, G c) = ∑ a, ∑ b, ∑ c, F a b * G c := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_mul_sum]

theorem sums3_mul (F : Fin n → Fin n → Fin n → ℝ) (G : Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, F a b c) * (∑ d, G d) = ∑ a, ∑ b, ∑ c, ∑ d, F a b c * G d := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_mul_sum]

theorem sum4_mul_one (F : Fin n → Fin n → Fin n → Fin n → ℝ) (U : ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) * U = ∑ a, ∑ b, ∑ c, ∑ d, F a b c d * U := by
  rw [Finset.sum_mul Finset.univ (fun a => ∑ b, ∑ c, ∑ d, F a b c d) U]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_mul Finset.univ (fun b => ∑ c, ∑ d, F a b c d) U]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_mul Finset.univ (fun c => ∑ d, F a b c d) U]
  apply Finset.sum_congr rfl; intro c _
  rw [Finset.sum_mul Finset.univ (fun d => F a b c d) U]

theorem mul_sum4 (c : ℝ) (f g h k : Fin n → ℝ) :
    c * (∑ a, f a) * (∑ b, g b) * (∑ cc, h cc) * (∑ d, k d)
      = ∑ a, ∑ b, ∑ cc, ∑ d, c * f a * g b * h cc * k d := by
  have h1 : (c * (∑ a, f a)) * (∑ b, g b) = ∑ a, ∑ b, c * f a * g b := by
    rw [Finset.mul_sum Finset.univ f c,
      Finset.sum_mul_sum Finset.univ Finset.univ (fun a => c * f a) g]
  rw [h1]
  have h2 : (∑ a, ∑ b, c * f a * g b) * (∑ cc, h cc)
      = ∑ a, ∑ b, ∑ cc, c * f a * g b * h cc := sums2_mul _ _
  rw [h2]
  exact sums3_mul (fun a b cc => c * f a * g b * h cc) k

/-- Swapping the two blocks of four indices of an eight-fold sum. -/
theorem sum4_4_swap (Ψ : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, ∑ a, ∑ b, ∑ c, ∑ d, Ψ i j k l a b c d)
      = ∑ a, ∑ b, ∑ c, ∑ d, ∑ i, ∑ j, ∑ k, ∑ l, Ψ i j k l a b c d := by
  have h1 : (∑ p : Fin n × Fin n × Fin n × Fin n, ∑ q : Fin n × Fin n × Fin n × Fin n,
      Ψ p.1 p.2.1 p.2.2.1 p.2.2.2 q.1 q.2.1 q.2.2.1 q.2.2.2)
      = ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, ∑ b, ∑ c, ∑ d, Ψ i j k l a b c d := by
    simp [Fintype.sum_prod_type]
  have h2 : (∑ p : Fin n × Fin n × Fin n × Fin n, ∑ q : Fin n × Fin n × Fin n × Fin n,
      Ψ p.1 p.2.1 p.2.2.1 p.2.2.2 q.1 q.2.1 q.2.2.1 q.2.2.2)
      = ∑ a, ∑ b, ∑ c, ∑ d, ∑ i, ∑ j, ∑ k, ∑ l, Ψ i j k l a b c d := by
    rw [Finset.sum_comm]
    simp [Fintype.sum_prod_type]
  exact h1.symm.trans h2


/-! ## Linearity of `R4` and of `EF` in the tensor variable -/

theorem R4_add_tensor (R S : Curv4 n) (a b c d : Fin n → ℝ) :
    R4 (R + S) a b c d = R4 R a b c d + R4 S a b c d := by
  simp only [R4, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem R4_smul_tensor (t : ℝ) (R : Curv4 n) (a b c d : Fin n → ℝ) :
    R4 (t • R) a b c d = t * R4 R a b c d := by
  simp only [R4, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  ring

theorem EF_add (R S : Curv4 n) (x y z w : Fin n → ℝ) :
    EF (R + S) x y z w = EF R x y z w + EF S x y z w := by
  simp only [EF, R4_add_tensor]
  ring

theorem EF_smul (t : ℝ) (R : Curv4 n) (x y z w : Fin n → ℝ) :
    EF (t • R) x y z w = t * EF R x y z w := by
  simp only [EF, R4_smul_tensor]
  ring

theorem EF_add_smul (a b : ℝ) (R S : Curv4 n) (x y z w : Fin n → ℝ) :
    EF (a • R + b • S) x y z w = a * EF R x y z w + b * EF S x y z w := by
  simp only [EF, R4_add_tensor, R4_smul_tensor]
  ring

theorem EF_continuous (x y z w : Fin n → ℝ) :
    Continuous (fun R : Curv4 n => EF R x y z w) := by
  simp only [EF, R4]
  fun_prop

/-! ## Closedness, convexity, cone and additive structure -/

theorem isClosed_inPIC2 (n : ℕ) : IsClosed {R : Curv4 n | InPIC2 R} := by
  have h : {R : Curv4 n | InPIC2 R} =
      ⋂ (x : Fin n → ℝ), ⋂ (y : Fin n → ℝ), ⋂ (z : Fin n → ℝ), ⋂ (w : Fin n → ℝ),
        {R : Curv4 n | 0 ≤ EF R x y z w} := by
    ext R
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, inPIC2_iff]
  rw [h]
  exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z =>
    isClosed_iInter fun w => isClosed_le continuous_const (EF_continuous x y z w)

theorem convex_inPIC2 (n : ℕ) : Convex ℝ {R : Curv4 n | InPIC2 R} := by
  intro R hR S hS a b ha hb _ x y z w
  change 0 ≤ EF (a • R + b • S) x y z w
  rw [EF_add_smul]
  exact add_nonneg (mul_nonneg ha (hR x y z w)) (mul_nonneg hb (hS x y z w))

theorem inPIC2_smul {R : Curv4 n} (hR : InPIC2 R) {c : ℝ} (hc : 0 ≤ c) : InPIC2 (c • R) := by
  intro x y z w
  change 0 ≤ EF (c • R) x y z w
  rw [EF_smul]
  exact mul_nonneg hc (hR x y z w)

theorem inPIC2_add {R S : Curv4 n} (hR : InPIC2 R) (hS : InPIC2 S) : InPIC2 (R + S) := by
  intro x y z w
  change 0 ≤ EF (R + S) x y z w
  rw [EF_add]
  exact add_nonneg (hR x y z w) (hS x y z w)

/-! ## The round sphere lies in the cone -/

/-- `R4` of the Kronecker-delta tensor `Iso n`. -/
theorem r4_iso (n : ℕ) (a b c d : Fin n → ℝ) :
    R4 (Iso n) a b c d = dot a c * dot b d - dot a d * dot b c := by
  have key1 : ∀ i j : Fin n,
      (∑ k, ∑ l, ((if i = k then (1:ℝ) else 0) * (if j = l then 1 else 0)) * (a i * b j * c k * d l))
        = a i * b j * c i * d j := by
    intro i j
    exact delta_pair (fun k => a i * b j * c k) (fun l => d l) i j
  have key2 : ∀ i j : Fin n,
      (∑ k, ∑ l, ((if i = l then (1:ℝ) else 0) * (if j = k then 1 else 0)) * (a i * b j * c k * d l))
        = a i * b j * d i * c j := by
    intro i j
    have h := delta_pair (fun k => a i * b j * c k) (fun l => d l) j i
    rw [show (∑ k, ∑ l, ((if i = l then (1:ℝ) else 0) * (if j = k then 1 else 0)) * (a i * b j * c k * d l))
        = (∑ k, ∑ l, ((if j = k then (1:ℝ) else 0) * (if i = l then 1 else 0)) * (a i * b j * c k * d l)) from ?_]
    · rw [h]; ring
    · apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro l _
      ring
  simp only [R4, Iso, dot]
  rw [Finset.sum_mul_sum (Finset.univ) (Finset.univ) (fun i => a i * c i) (fun j => b j * d j),
      Finset.sum_mul_sum (Finset.univ) (Finset.univ) (fun i => a i * d i) (fun j => b j * c j)]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _
  rw [show (∑ k, ∑ l, ((if i = k then (1:ℝ) else 0) * (if j = l then 1 else 0) - (if i = l then (1:ℝ) else 0) * (if j = k then 1 else 0)) * a i * b j * c k * d l)
      = (∑ k, ∑ l, ((if i = k then (1:ℝ) else 0) * (if j = l then 1 else 0)) * (a i * b j * c k * d l))
        - (∑ k, ∑ l, ((if i = l then (1:ℝ) else 0) * (if j = k then 1 else 0)) * (a i * b j * c k * d l)) from ?_]
  · rw [key1 i j, key2 i j]; ring
  · rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro l _
    ring

/-- The expansion of `EF (Iso n)` as a difference of a product and a sum of two squares. -/
theorem EF_iso (n : ℕ) (x y z w : Fin n → ℝ) :
    EF (Iso n) x y z w = (dot x x + dot y y) * (dot z z + dot w w) -
      ((dot x z + dot y w) ^ 2 + (dot y z - dot x w) ^ 2) := by
  rw [EF, r4_iso, r4_iso, r4_iso, r4_iso, r4_iso,
    dot_comm z x, dot_comm w x, dot_comm z y, dot_comm w y]
  ring

theorem dot_cs (n : ℕ) (x y z w : Fin n → ℝ) :
    (dot x z + dot y w) ^ 2 + (dot y z - dot x w) ^ 2 ≤
      (dot x x + dot y y) * (dot z z + dot w w) := by
  have key := pair_cs (fun i => x i * z i + y i * w i) (fun i => y i * z i - x i * w i)
    (fun i => x i ^ 2 + y i ^ 2) (fun i => z i ^ 2 + w i ^ 2)
    (fun i => by ring)
    (fun i => by positivity)
    (fun i => by positivity)
  have e1 : (∑ i, (x i * z i + y i * w i)) = dot x z + dot y w := by
    simp only [dot, Finset.sum_add_distrib]
  have e2 : (∑ i, (y i * z i - x i * w i)) = dot y z - dot x w := by
    simp only [dot, Finset.sum_sub_distrib]
  have e3 : (∑ i, (x i ^ 2 + y i ^ 2)) = dot x x + dot y y := by
    simp only [dot, pow_two, Finset.sum_add_distrib]
  have e4 : (∑ i, (z i ^ 2 + w i ^ 2)) = dot z z + dot w w := by
    simp only [dot, pow_two, Finset.sum_add_distrib]
  rw [e1, e2, e3, e4] at key
  exact key

theorem inPIC2_iso (n : ℕ) : InPIC2 (Iso n) := by
  intro x y z w
  change 0 ≤ EF (Iso n) x y z w
  rw [EF_iso]
  have h := dot_cs n x y z w
  linarith

theorem inPIC2_sub_smul_half (n : ℕ) :
    InPIC2 (Iso n - (1 / 2 : ℝ) • Iso n) := by
  have hsub : Iso n - (1 / 2 : ℝ) • Iso n = (1 / 2 : ℝ) • Iso n := by
    ext i j k l
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsub]
  exact inPIC2_smul (inPIC2_iso n) (by norm_num)

/-! ## Frame invariance -/

/-- `R4` is transported by `rot`: the four vector slots are pulled back by the transpose. -/
theorem r4_rot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n)
    (x y z w : Fin n → ℝ) :
    R4 (rot A R) x y z w =
      R4 R (A.transpose.mulVec x) (A.transpose.mulVec y) (A.transpose.mulVec z) (A.transpose.mulVec w) := by
  have hLHS : R4 (rot A R) x y z w
      = ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, ∑ b, ∑ c, ∑ d,
          R a b c d * (A i a * x i) * (A j b * y j) * (A k c * z k) * (A l d * w l) := by
    simp only [R4, rot]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    rw [show (∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * R a b c d) * x i * y j * z k * w l
        = (∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * R a b c d)
            * (x i * y j * z k * w l) from by ring]
    rw [sum4_mul_one]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro d _
    ring
  have hRHS : R4 R (A.transpose.mulVec x) (A.transpose.mulVec y) (A.transpose.mulVec z)
        (A.transpose.mulVec w)
      = ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, ∑ b, ∑ c, ∑ d,
          R i j k l * (A a i * x a) * (A b j * y b) * (A c k * z c) * (A d l * w d) := by
    simp only [R4, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    rw [mul_sum4]
  calc R4 (rot A R) x y z w
      = ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, ∑ b, ∑ c, ∑ d,
          R a b c d * (A i a * x i) * (A j b * y j) * (A k c * z k) * (A l d * w l) := hLHS
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ i, ∑ j, ∑ k, ∑ l,
          R a b c d * (A i a * x i) * (A j b * y j) * (A k c * z k) * (A l d * w l) :=
        sum4_4_swap (fun i j k l a b c d =>
          R a b c d * (A i a * x i) * (A j b * y j) * (A k c * z k) * (A l d * w l))
    _ = ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, ∑ b, ∑ c, ∑ d,
          R i j k l * (A a i * x a) * (A b j * y b) * (A c k * z c) * (A d l * w d) := rfl
    _ = R4 R (A.transpose.mulVec x) (A.transpose.mulVec y) (A.transpose.mulVec z)
        (A.transpose.mulVec w) := hRHS.symm

theorem inPIC2_rot (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) (hR : InPIC2 R) :
    InPIC2 (rot A R) := by
  intro x y z w
  change 0 ≤ EF (rot A R) x y z w
  have h : EF (rot A R) x y z w = EF R (A.transpose.mulVec x) (A.transpose.mulVec y)
      (A.transpose.mulVec z) (A.transpose.mulVec w) := by
    simp only [EF, r4_rot]
  rw [h]
  exact hR _ _ _ _

end Cone

theorem inPIC2_cone_basic (n : ℕ) :
    IsClosed {R : Submission.Diff.Alg.Curv4 n | Submission.Diff.Alg.InPIC2 R} ∧
    Convex ℝ {R : Submission.Diff.Alg.Curv4 n | Submission.Diff.Alg.InPIC2 R} ∧
    (∀ R : Submission.Diff.Alg.Curv4 n, Submission.Diff.Alg.InPIC2 R → ∀ c : ℝ, 0 ≤ c →
      Submission.Diff.Alg.InPIC2 (c • R)) ∧
    (∀ R S : Submission.Diff.Alg.Curv4 n, Submission.Diff.Alg.InPIC2 R →
      Submission.Diff.Alg.InPIC2 S → Submission.Diff.Alg.InPIC2 (R + S)) ∧
    Submission.Diff.Alg.InPIC2 (Submission.Diff.Alg.Iso n) ∧
    Submission.Diff.Alg.InPIC2 (Submission.Diff.Alg.Iso n - (1 / 2 : ℝ) • Submission.Diff.Alg.Iso n) ∧
    (∀ A : Matrix (Fin n) (Fin n) ℝ, A ∈ Matrix.orthogonalGroup (Fin n) ℝ →
      ∀ R : Submission.Diff.Alg.Curv4 n, Submission.Diff.Alg.InPIC2 R →
        Submission.Diff.Alg.InPIC2 (Submission.Diff.Alg.rot A R)) := by
  refine ⟨Cone.isClosed_inPIC2 n, Cone.convex_inPIC2 n, ?_, ?_, Cone.inPIC2_iso n,
    Cone.inPIC2_sub_smul_half n, ?_⟩
  · intro R hR c hc
    exact Cone.inPIC2_smul hR hc
  · intro R S hR hS
    exact Cone.inPIC2_add hR hS
  · intro A _ R hR
    exact Cone.inPIC2_rot n A R hR

end Work.Diff.Alg.Pinch
