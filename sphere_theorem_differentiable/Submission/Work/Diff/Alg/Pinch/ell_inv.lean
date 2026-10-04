import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Strict
import Submission.Work.Diff.Alg.Pinch.ric_knProd_id2
import Submission.Work.Diff.Alg.Pinch.scalAlg_knProd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Inverting the Böhm–Wilking transformation `ℓ_{a,b}`

The Böhm–Wilking linear transformation
`ℓ_{a,b}(R) = R + b · (Ric₀(R) ∧ id) + (a/n · scal R) · (id ∧ id)`
(`Work.Diff.Alg.Pinch.ell`) is inverted by
`R ↦ R − (b / (1 + (n−2)b)) · (Ric₀(R) ∧ id) − ((a/n)/(1 + 2(n−1)a) · scal R) · (id ∧ id)`.

The reason is that `Ric₀` and `scal` scale in a controlled way:

* `Ric₀(ℓ_{a,b} R) = (1 + (n−2)b) · Ric₀ R`
* `scal(ℓ_{a,b} R) = (1 + 2(n−1)a) · scal R`

so the two correction terms are exactly designed to cancel the `Ric₀` and `scal` parts of `ℓ`.
This file establishes the main content, namely that the components of the corrected tensor
`T = S − β · (Ric₀ S ∧ id) − γ · (id ∧ id)` (`β = b/(1+(n−2)b)`, `γ = (a/n)/(1+2(n−1)a)·scal S`)
satisfy

* `Ric₀ T = (1 + (n−2)b)⁻¹ · Ric₀ S`
* `scal T = (1 + 2(n−1)a)⁻¹ · scal S`,

whence `ℓ_{a,b} T = S`.

The component computations rest on the contraction formulas
`ric (A ∧ id) = (tr A) · id + (n−2) A` and `scal (A ∧ B) = 2(tr A · tr B − tr(A·B))`,
together with `tr (Ric₀ S) = 0`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Linearities -/

lemma ellinv_ric_sub (A B : Curv4 n) (i j : Fin n) :
    ric (A - B) i j = ric A i j - ric B i j := by
  simp only [ric, Pi.sub_apply, Finset.sum_sub_distrib]

lemma ellinv_ric_smul (c : ℝ) (A : Curv4 n) (i j : Fin n) :
    ric (c • A) i j = c * ric A i j := by
  simp only [ric, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

lemma ellinv_scalAlg_sub (A B : Curv4 n) :
    scalAlg (A - B) = scalAlg A - scalAlg B := by
  simp only [scalAlg, Pi.sub_apply, Finset.sum_sub_distrib]

lemma ellinv_scalAlg_smul (c : ℝ) (A : Curv4 n) :
    scalAlg (c • A) = c * scalAlg A := by
  simp only [scalAlg, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

lemma ellinv_knProd_smul_left (c : ℝ) (A B : Fin n → Fin n → ℝ) :
    knProd (c • A) B = c • knProd A B := by
  funext i j k l
  simp only [knProd, Pi.smul_apply, smul_eq_mul]
  ring

/-! ## Contractions of elementary `2`-tensors -/

/-- `∑ j, f j * δ_{j i} = f i`. -/
lemma ellinv_sum_mul_id2 (f : Fin n → ℝ) (i : Fin n) : ∑ j, f j * id2 n j i = f i := by
  rw [Finset.sum_eq_single i]
  · simp [id2]
  · intro j _ hj; simp [id2, if_neg hj]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- `∑ j, δ_{i j} * f j = f i`. -/
lemma ellinv_sum_id2_mul (f : Fin n → ℝ) (i : Fin n) : ∑ j, id2 n i j * f j = f i := by
  rw [Finset.sum_eq_single i]
  · simp [id2]
  · intro j _ hj; simp [id2, if_neg (Ne.symm hj)]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The trace of the traceless Ricci tensor vanishes: `∑ i, Ric₀(R)ᵢᵢ = 0`. -/
lemma ellinv_sum_ric0_diag {S : Curv4 n} (hS : IsAlgCurv S) : ∑ i, ric0 S i i = 0 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp h)
    have hdiag : ∑ i, ric S i i = scalAlg S := by
      simp only [ric, scalAlg]; rw [Finset.sum_comm]
    have hid : ∑ i : Fin n, id2 n i i = (n : ℝ) := by
      simp [id2, Finset.sum_const, nsmul_eq_mul]
    have hsum : ∑ i, ric0 S i i
        = (∑ i, ric S i i) - (scalAlg S / (n : ℝ)) * (∑ i, id2 n i i) := by
      simp only [ric0, Finset.sum_sub_distrib]
      rw [Finset.mul_sum]
    rw [hsum, hdiag, hid]
    field_simp
    ring

/-- The Ricci contraction of `Ric₀(R) ∧ id`: since `tr Ric₀ = 0`, only the `(n−2)`-term survives. -/
lemma ellinv_ric_knProd_ric0 {S : Curv4 n} (hS : IsAlgCurv S) (i j : Fin n) :
    ric (knProd (ric0 S) (id2 n)) i j = ((n : ℝ) - 2) * ric0 S i j := by
  rw [ric_knProd_id2, ellinv_sum_ric0_diag hS]
  ring

/-- The Ricci contraction of `id ∧ id` is `(2n−2) · id`. -/
lemma ellinv_ric_knProd_id2_id2 (i j : Fin n) :
    ric (knProd (id2 n) (id2 n)) i j = (2 * (n : ℝ) - 2) * id2 n i j := by
  rw [ric_knProd_id2]
  have h : (∑ k : Fin n, id2 n k k) = (n : ℝ) := by
    simp [id2, Finset.sum_const, nsmul_eq_mul]
  rw [h, ← id2]
  ring

/-- `scal (Ric₀(R) ∧ id) = 0`. -/
lemma ellinv_scalAlg_knProd_ric0 {S : Curv4 n} (hS : IsAlgCurv S) :
    scalAlg (knProd (ric0 S) (id2 n)) = 0 := by
  rw [scalAlg_knProd]
  have h1 : ∑ i, ric0 S i i = 0 := ellinv_sum_ric0_diag hS
  have h2 : ∑ i, ∑ j, ric0 S i j * id2 n j i = 0 := by
    rw [show (∑ i, ∑ j, ric0 S i j * id2 n j i) = ∑ i, ric0 S i i from
      Finset.sum_congr rfl (fun i _ => ellinv_sum_mul_id2 (fun j => ric0 S i j) i)]
    exact h1
  rw [h1, h2]
  ring

/-- `scal (id ∧ id) = (2n−2) · n`. -/
lemma ellinv_scalAlg_knProd_id2_id2 (n : ℕ) :
    scalAlg (knProd (id2 n) (id2 n)) = (2 * (n : ℝ) - 2) * (n : ℝ) := by
  rw [scalAlg_knProd]
  have h1 : ∑ i, id2 n i i = (n : ℝ) := by
    simp [id2, Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ i, ∑ j, id2 n i j * id2 n j i = (n : ℝ) := by
    rw [show (∑ i, ∑ j, id2 n i j * id2 n j i) = ∑ i, id2 n i i from
      Finset.sum_congr rfl (fun i _ => ellinv_sum_id2_mul (fun j => id2 n j i) i)]
    exact h1
  rw [h1, h2]
  ring

/-! ## The two scalar identities behind the inverse

Both are elementary identities in `ℝ`; abstracting the two denominators
`1 + 2(n−1)a` and `1 + (n−2)b` into local variables makes `field_simp` deal with them as
atoms, after which `ring` finishes. -/

lemma ellinv_scal_arith (n : ℕ) (a : ℝ) (ha : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0)
    (hn : (n : ℝ) ≠ 0) (scal : ℝ) :
    scal - (a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * scal * ((2 * (n : ℝ) - 2) * (n : ℝ))
      = scal / (1 + 2 * ((n : ℝ) - 1) * a) := by
  set D : ℝ := 1 + 2 * ((n : ℝ) - 1) * a with hDd
  have hD : D ≠ 0 := by rw [hDd]; exact ha
  field_simp
  rw [hDd]
  ring

lemma ellinv_ric_arith (n : ℕ) (a b r s d : ℝ)
    (ha : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0) (hb : 1 + ((n : ℝ) - 2) * b ≠ 0)
    (hn : (n : ℝ) ≠ 0) :
    r + s / (n : ℝ) * d - (b / (1 + ((n : ℝ) - 2) * b)) * ((n : ℝ) - 2) * r
        - ((a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * s) * ((2 * (n : ℝ) - 2) * d)
        - ((s / (1 + 2 * ((n : ℝ) - 1) * a)) / (n : ℝ)) * d
      = (1 / (1 + ((n : ℝ) - 2) * b)) * r := by
  set Eb : ℝ := 1 + ((n : ℝ) - 2) * b with hEbd
  set D : ℝ := 1 + 2 * ((n : ℝ) - 1) * a with hDd
  have hEb : Eb ≠ 0 := by rw [hEbd]; exact hb
  have hD : D ≠ 0 := by rw [hDd]; exact ha
  field_simp
  rw [hEbd, hDd]
  ring

/-! ## The inverse -/

theorem ell_inv (n : ℕ) {a b : ℝ} (ha : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0)
    (hb : 1 + ((n : ℝ) - 2) * b ≠ 0) {S : Submission.Diff.Alg.Curv4 n}
    (hS : Submission.Diff.Alg.IsAlgCurv S) :
    Work.Diff.Alg.Pinch.ell a b (S - (b / (1 + ((n : ℝ) - 2) * b)) •
          Work.Diff.Alg.Pinch.knProd (Work.Diff.Alg.Pinch.ric0 S) (Work.Diff.Alg.Pinch.id2 n) -
        ((a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * Submission.Diff.Alg.scalAlg S) •
          Work.Diff.Alg.Pinch.knProd (Work.Diff.Alg.Pinch.id2 n) (Work.Diff.Alg.Pinch.id2 n)) = S := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- for `n = 0` both sides are functions on the empty type
    subst hn0
    funext i
    exact i.elim0
  · have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hnpos)
    set K1 : Curv4 n := knProd (ric0 S) (id2 n) with hK1
    set K2 : Curv4 n := knProd (id2 n) (id2 n) with hK2
    set c1 : ℝ := b / (1 + ((n : ℝ) - 2) * b) with hc1
    set c2 : ℝ := (a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg S with hc2
    set T : Curv4 n := S - c1 • K1 - c2 • K2 with hT
    -- the components of `T`
    have hricT : ∀ i j, ric T i j = ric S i j - c1 * ((n : ℝ) - 2) * ric0 S i j
        - c2 * ((2 * (n : ℝ) - 2) * id2 n i j) := by
      intro i j
      rw [hT, ellinv_ric_sub, ellinv_ric_sub, ellinv_ric_smul, ellinv_ric_smul, hK1, hK2,
        ellinv_ric_knProd_ric0 hS, ellinv_ric_knProd_id2_id2]
      ring
    have hscalT : scalAlg T = scalAlg S / (1 + 2 * ((n : ℝ) - 1) * a) := by
      rw [hT, ellinv_scalAlg_sub, ellinv_scalAlg_sub, ellinv_scalAlg_smul, ellinv_scalAlg_smul,
        hc1, hc2, hK1, hK2, ellinv_scalAlg_knProd_ric0 hS, ellinv_scalAlg_knProd_id2_id2 n]
      rw [mul_zero, sub_zero]
      exact ellinv_scal_arith n a ha hn (scalAlg S)
    have hric0T : ∀ i j, ric0 T i j = (1 / (1 + ((n : ℝ) - 2) * b)) * ric0 S i j := by
      intro i j
      conv_lhs => rw [ric0]
      rw [hricT i j, hscalT]
      have hricS : ric S i j = ric0 S i j + (scalAlg S / (n : ℝ)) * id2 n i j := by
        rw [ric0]; ring
      rw [hricS, hc1, hc2]
      exact ellinv_ric_arith n a b (ric0 S i j) (scalAlg S) (id2 n i j) ha hb hn
    have hric0fun : ric0 T = (1 / (1 + ((n : ℝ) - 2) * b)) • ric0 S := by
      funext i j
      rw [hric0T i j]
      simp only [Pi.smul_apply, smul_eq_mul]
    have hkn : knProd (ric0 T) (id2 n) = (1 / (1 + ((n : ℝ) - 2) * b)) • K1 := by
      rw [hric0fun, ellinv_knProd_smul_left, ← hK1]
    -- assemble
    rw [ell, hkn, hscalT]
    rw [smul_smul]
    have hbk : b * (1 / (1 + ((n : ℝ) - 2) * b)) = c1 := by rw [hc1]; ring
    rw [hbk]
    have hac : a / (n : ℝ) * (scalAlg S / (1 + 2 * ((n : ℝ) - 1) * a)) = c2 := by
      rw [hc2]; ring
    rw [hac, ← hK2, hT]
    abel

end Work.Diff.Alg.Pinch
