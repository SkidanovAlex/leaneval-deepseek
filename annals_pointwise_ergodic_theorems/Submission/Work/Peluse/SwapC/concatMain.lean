/-
# The main chain of `Work.Peluse.SwapC.concatStep` (the `1 ≤ s` case)

From the node's hypothesis `δ ≤ avg_i pbox (s+1) (qH i :: q₁ i) (0 :: q₂ i)` to the lower bound
`δ^{2^{2s+1}}/3^{2^{2s}} ≤ avg_p pbox (2s+1) (concatenated slots)`: step A (Cauchy–Schwarz and the
expansion of the squared gauge), step B (the raw split, the concatenation identification, the
Gowers–Cauchy–Schwarz inequality and the assembly), step C (the arithmetic), and finally the
Jensen + peel-back step `concatFinish`.
-/
import Mathlib
import Submission.Work.Peluse.SwapC.concatDefs
import Submission.Work.Peluse.SwapC.gauge_cs
import Submission.Work.Peluse.SwapC.pairObjRawSplit
import Submission.Work.Peluse.SwapC.concatIdentSumI
import Submission.Work.Peluse.SwapC.cFunICubeLe
import Submission.Work.Peluse.SwapC.concatFinalIdent

set_option autoImplicit false
set_option maxHeartbeats 3200000
open scoped BigOperators

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap

/-! ## 0. The objects of the chain -/

/-- The six-index form of `Zm`. -/
def Zm6 {I : Type} (s M N : ℕ) (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ) (f : ℤ → ℂ)
    (j : I × I × Fin M × Fin M × Fin M × Fin M) : ℝ :=
  Zm s M N qH q₁ q₂ f j.1 j.2.1 j.2.2.1 j.2.2.2.1 j.2.2.2.2.1 j.2.2.2.2.2

/-- The average of the `(1/2^{2s})`-th powers of the box powers `Zm`, over the six-fold index
type. -/
def ZmAvg {I : Type} [Fintype I] (s M N : ℕ) (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ)
    (f : ℤ → ℂ) : ℝ :=
  avg (fun j : I × I × Fin M × Fin M × Fin M × Fin M =>
    (Zm6 s M N qH q₁ q₂ f j) ^ (1 / (2 : ℝ) ^ (2 * s)))

/-- The nested sum of the same powers. -/
def ZmPowSum {I : Type} [Fintype I] (s M N : ℕ) (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ)
    (f : ℤ → ℂ) : ℝ :=
  ∑ i₀ : I, ∑ i₁ : I, ∑ a₀ : Fin M, ∑ a₀' : Fin M, ∑ a₁ : Fin M, ∑ a₁' : Fin M,
    (Zm s M N qH q₁ q₂ f i₀ i₁ a₀ a₀' a₁ a₁') ^ (1 / (2 : ℝ) ^ (2 * s))

/-- The normalising constant of the gauge. -/
def kappa {I : Type} [Fintype I] (s M : ℕ) : ℝ :=
  ‖(((M : ℂ) ^ 4)⁻¹) ^ (s + 1)‖ ^ 2 * ‖(((Fintype.card I : ℂ))⁻¹)‖ ^ 2

/-- The doubled `Rest`-product of the expansion of the squared gauge. -/
def pairSum {I : Type} [Fintype I] (s M : ℕ) (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ)
    (f : ℤ → ℂ) : ℂ :=
  ∑ i₀ : I, ∑ i₁ : I, ∑ H₀ : Fin (s + 1) → Fin M × Fin M,
    ∑ H₀' : Fin (s + 1) → Fin M × Fin M, ∑ H₁ : Fin (s + 1) → Fin M × Fin M,
      ∑ H₁' : Fin (s + 1) → Fin M × Fin M,
        pairObj s M qH q₁ q₂ f i₀ i₁ H₀ H₀' H₁ H₁'

/-- The doubled `Rest`-product at the four raw coordinates, with the second coordinates of the raw
slots frozen to `z`. -/
def pairObjRaw {I : Type} (s M : ℕ) (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ) (f : ℤ → ℂ)
    (z : Fin M) (i₀ i₁ : I) (a₀ a₀' a₁ a₁' : Fin M) (k₀ k₀' k₁ k₁' : Fin s → Fin M × Fin M) : ℂ :=
  pairObj s M qH q₁ q₂ f i₀ i₁ (Fin.cons (a₀, z) k₀) (Fin.cons (a₀', z) k₀')
    (Fin.cons (a₁, z) k₁) (Fin.cons (a₁', z) k₁')

/-- The `2s`-fold multiset cube sum with the truncated corner family `cFunI`. -/
def cFunCube {I : Type} (s M N : ℕ) (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ) (f : ℤ → ℂ) (x₀ : ℤ)
    (i₀ i₁ : I) (a₀ a₀' a₁ a₁' : Fin M) : ℂ :=
  mCubeSum (2 * s) (Fin M × Fin M) (catDir M (q₁ i₀) (q₂ i₀) (q₁ i₁) (q₂ i₁))
    (symIcc N) (cFunI s f x₀ (rawIncr qH i₀ a₀ a₀') (rawIncr qH i₁ a₁ a₁') N)

/-- The nested sum of the four-fold `pairObj` sums. -/
def pairObjRawSum {I : Type} [Fintype I] (s M : ℕ) (z : Fin M) (qH : I → ℤ)
    (q₁ q₂ : I → Fin s → ℤ) (f : ℤ → ℂ) : ℂ :=
  ∑ i₀ : I, ∑ i₁ : I, ∑ a₀ : Fin M, ∑ a₀' : Fin M, ∑ a₁ : Fin M, ∑ a₁' : Fin M,
    ∑ k₀ : Fin s → Fin M × Fin M, ∑ k₀' : Fin s → Fin M × Fin M,
      ∑ k₁ : Fin s → Fin M × Fin M, ∑ k₁' : Fin s → Fin M × Fin M,
        pairObjRaw s M qH q₁ q₂ f z i₀ i₁ a₀ a₀' a₁ a₁' k₀ k₀' k₁ k₁'

@[simp] lemma cFunCube_eq {I : Type} (s M N : ℕ) (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ)
    (f : ℤ → ℂ) (x₀ : ℤ) (i₀ i₁ : I) (a₀ a₀' a₁ a₁' : Fin M) :
    cFunCube s M N qH q₁ q₂ f x₀ i₀ i₁ a₀ a₀' a₁ a₁'
      = mCubeSum (2 * s) (Fin M × Fin M) (catDir M (q₁ i₀) (q₂ i₀) (q₁ i₁) (q₂ i₁))
          (symIcc N) (cFunI s f x₀ (rawIncr qH i₀ a₀ a₀') (rawIncr qH i₁ a₁ a₁') N) := rfl

@[simp] lemma pairObjRaw_eq {I : Type} (s M : ℕ) (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ)
    (f : ℤ → ℂ) (z : Fin M) (i₀ i₁ : I) (a₀ a₀' a₁ a₁' : Fin M)
    (k₀ k₀' k₁ k₁' : Fin s → Fin M × Fin M) :
    pairObjRaw s M qH q₁ q₂ f z i₀ i₁ a₀ a₀' a₁ a₁' k₀ k₀' k₁ k₁'
      = pairObj s M qH q₁ q₂ f i₀ i₁ (Fin.cons (a₀, z) k₀) (Fin.cons (a₀', z) k₀')
          (Fin.cons (a₁, z) k₁) (Fin.cons (a₁', z) k₁') := rfl

/-- The real part of `↑n * (↑m)^k * z`. -/
lemma re_natCast_mul_natCast_pow_mul (n m k : ℕ) (z : ℂ) :
    (((n : ℂ) * ((m : ℂ) ^ k) * z).re) = ((n : ℝ) * ((m : ℝ) ^ k)) * z.re := by
  have h : (n : ℂ) * ((m : ℂ) ^ k) = ((((n : ℝ) * ((m : ℝ) ^ k)) : ℝ) : ℂ) := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) from rfl, show (m : ℂ) = ((m : ℝ) : ℂ) from rfl,
      ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  rw [show (((n : ℂ) * ((m : ℂ) ^ k) * z).re) = ((((n : ℂ) * ((m : ℂ) ^ k)) * z).re) from rfl,
    h, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The real part of `(↑m)^k * z`. -/
lemma re_natCast_pow_mul (m k : ℕ) (z : ℂ) :
    ((((m : ℂ) ^ k) * z).re) = ((m : ℝ) ^ k) * z.re := by
  have h : ((m : ℂ) ^ k) = (((m : ℝ) ^ k : ℝ) : ℂ) := by
    rw [show (m : ℂ) = ((m : ℝ) : ℂ) from rfl, ← Complex.ofReal_pow]
  rw [h, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma pairObjRawSum_eq {I : Type} [Fintype I] (s M : ℕ) (z : Fin M) (qH : I → ℤ)
    (q₁ q₂ : I → Fin s → ℤ) (f : ℤ → ℂ) :
    pairObjRawSum s M z qH q₁ q₂ f =
      ∑ i₀ : I, ∑ i₁ : I, ∑ a₀ : Fin M, ∑ a₀' : Fin M, ∑ a₁ : Fin M, ∑ a₁' : Fin M,
        ∑ k₀ : Fin s → Fin M × Fin M, ∑ k₀' : Fin s → Fin M × Fin M,
          ∑ k₁ : Fin s → Fin M × Fin M, ∑ k₁' : Fin s → Fin M × Fin M,
            pairObjRaw s M qH q₁ q₂ f z i₀ i₁ a₀ a₀' a₁ a₁' k₀ k₀' k₁ k₁' := rfl

lemma ZmPowSum_eq {I : Type} [Fintype I] (s M N : ℕ) (qH : I → ℤ)
    (q₁ q₂ : I → Fin s → ℤ) (f : ℤ → ℂ) :
    ZmPowSum s M N qH q₁ q₂ f =
      ∑ i₀ : I, ∑ i₁ : I, ∑ a₀ : Fin M, ∑ a₀' : Fin M, ∑ a₁ : Fin M, ∑ a₁' : Fin M,
        (Zm s M N qH q₁ q₂ f i₀ i₁ a₀ a₀' a₁ a₁') ^ (1 / (2 : ℝ) ^ (2 * s)) := rfl

/-! ## 1. Sum-manipulation helpers -/

/-- A sum over the six-fold product type, expanded to its nested form. -/
lemma sumJ_eq {I : Type} [Fintype I] {M : ℕ}
    (F : I → I → Fin M → Fin M → Fin M → Fin M → ℝ) :
    (∑ j : I × I × Fin M × Fin M × Fin M × Fin M,
        F j.1 j.2.1 j.2.2.1 j.2.2.2.1 j.2.2.2.2.1 j.2.2.2.2.2)
      = ∑ i : I, ∑ j : I, ∑ a : Fin M, ∑ b : Fin M, ∑ c : Fin M, ∑ d : Fin M,
          F i j a b c d := by
  simp only [Fintype.sum_prod_type]

/-- Monotonicity of a six-fold nested sum (with a complex-valued summand). -/
lemma sum6_le_re {I : Type} [Fintype I] {M : ℕ}
    {F : I → I → Fin M → Fin M → Fin M → Fin M → ℝ}
    {G : I → I → Fin M → Fin M → Fin M → Fin M → ℂ}
    (h : ∀ i j a b c d, F i j a b c d ≤ (G i j a b c d).re) :
    (∑ i : I, ∑ j : I, ∑ a : Fin M, ∑ b : Fin M, ∑ c : Fin M, ∑ d : Fin M, F i j a b c d)
      ≤ (∑ i : I, ∑ j : I, ∑ a : Fin M, ∑ b : Fin M, ∑ c : Fin M, ∑ d : Fin M,
          G i j a b c d).re := by
  rw [Complex.re_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  exact h i j a b c d

/-- The cardinality of the six-fold index type. -/
lemma cardJ_eq {I : Type} [Fintype I] {M : ℕ} :
    (Fintype.card (I × I × Fin M × Fin M × Fin M × Fin M) : ℝ)
      = ((Fintype.card I : ℝ)) ^ 2 * (M : ℝ) ^ 4 := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  push_cast
  ring

/-! ## 2. The arithmetic of `kappa` -/

lemma kappa_pos {I : Type} [Fintype I] [Nonempty I] {s M : ℕ} (hM : 1 ≤ M) :
    0 < kappa (I := I) s M := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have h1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hcardpos : (0 : ℝ) < (Fintype.card I : ℝ) := by
    have hpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ‹Nonempty I›
    exact_mod_cast hpos
  rw [kappa]
  have h1 : 0 < ‖(((M : ℂ) ^ 4)⁻¹) ^ (s + 1)‖ := by
    rw [norm_pow, norm_inv, norm_pow, Complex.norm_natCast]
    positivity
  have h2 : 0 < ‖(((Fintype.card I : ℂ))⁻¹)‖ := by
    rw [norm_inv, Complex.norm_natCast]
    positivity
  positivity

/-- **Step C: the arithmetic.**  `κ · M^4 · |X|^{4s} · |J| = 1`, so the normalising constants of
steps A and B cancel. -/
lemma kappaArith {I : Type} [Fintype I] [Nonempty I] {s M : ℕ} (hM : 1 ≤ M) :
    kappa (I := I) s M * (M : ℝ) ^ 4 * ((Fintype.card (Fin M × Fin M) : ℝ) ^ (4 * s)) *
      ((Fintype.card (I × I × Fin M × Fin M × Fin M × Fin M) : ℝ)) = 1 := by
  have hcardX : (Fintype.card (Fin M × Fin M) : ℝ) = (M : ℝ) ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  have hcardI : (Fintype.card I : ℝ) ≠ 0 := by
    have hpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ‹Nonempty I›
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hpos)
  have hnormM : ‖(((M : ℂ) ^ 4)⁻¹) ^ (s + 1)‖ = (((M : ℝ) ^ 4)⁻¹) ^ (s + 1) := by
    rw [norm_pow, norm_inv, norm_pow, Complex.norm_natCast]
  have hnormI : ‖(((Fintype.card I : ℂ))⁻¹)‖ = ((Fintype.card I : ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  rw [kappa, cardJ_eq, hcardX, hnormM, hnormI]
  have hM41 : (((M : ℝ) ^ 4)⁻¹) ^ (s + 1) * ((M : ℝ) ^ 4) ^ (s + 1) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (by positivity), one_pow]
  have hsq : ((((M : ℝ) ^ 4)⁻¹) ^ (s + 1)) ^ 2 * (((M : ℝ) ^ 4) ^ (s + 1)) ^ 2 = 1 := by
    rw [← mul_pow, hM41, one_pow]
  have hI : ((Fintype.card I : ℝ))⁻¹ ^ 2 * ((Fintype.card I : ℝ)) ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hcardI, one_pow]
  have hb : (M : ℝ) ^ 4 * ((M : ℝ) ^ 2) ^ (4 * s) * (M : ℝ) ^ 4 =
      (((M : ℝ) ^ 4) ^ (s + 1)) ^ 2 := by
    have e5 : ((M : ℝ) ^ 2) ^ (4 * s) = ((M : ℝ) ^ 4) ^ (2 * s) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    have hL : (M : ℝ) ^ 4 * ((M : ℝ) ^ 4) ^ (2 * s) * (M : ℝ) ^ 4 =
        ((M : ℝ) ^ 4) ^ (2 * s + 2) := by
      rw [← pow_succ', ← pow_succ]
    have hR : (((M : ℝ) ^ 4) ^ (s + 1)) ^ 2 = ((M : ℝ) ^ 4) ^ ((s + 1) * 2) := by
      rw [← pow_mul]
    rw [e5, hL, hR]
    congr 1
    omega
  calc ((((M : ℝ) ^ 4)⁻¹) ^ (s + 1)) ^ 2 * ((Fintype.card I : ℝ))⁻¹ ^ 2 * (M : ℝ) ^ 4 *
        ((M : ℝ) ^ 2) ^ (4 * s) * ((Fintype.card I : ℝ) ^ 2 * (M : ℝ) ^ 4)
      = ((((M : ℝ) ^ 4)⁻¹) ^ (s + 1)) ^ 2 *
        ((M : ℝ) ^ 4 * ((M : ℝ) ^ 2) ^ (4 * s) * (M : ℝ) ^ 4) *
        (((Fintype.card I : ℝ))⁻¹ ^ 2 * ((Fintype.card I : ℝ)) ^ 2) := by ring
    _ = ((((M : ℝ) ^ 4)⁻¹) ^ (s + 1)) ^ 2 * (((M : ℝ) ^ 4) ^ (s + 1)) ^ 2 *
        (((Fintype.card I : ℝ))⁻¹ ^ 2 * ((Fintype.card I : ℝ)) ^ 2) := by rw [hb]
    _ = 1 := by rw [hsq, hI]; ring

/-! ## 3. Step A: Cauchy–Schwarz and the expansion of the squared gauge -/

/-- **Step A.**  The node's hypothesis implies `δ²|S| ≤ κ · (pairSum).re`. -/
theorem stepA {I : Type} [Fintype I] [Nonempty I] (s M N : ℕ) (qH : I → ℤ)
    (q₁ q₂ : I → Fin s → ℤ) (δ : ℝ) (f : ℤ → ℂ) (x₀ : ℤ) (hM : 1 ≤ M) (hδ : 0 < δ)
    (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1) (hsup : ∀ x : ℤ, (N : ℤ) < |x - x₀| → f x = 0)
    (hfin : FinSuppZ f)
    (h : δ ≤ avg (fun i : I =>
        pbox (s + 1) (Fin.cons (qH i) (q₁ i)) (Fin.cons (0 : ℤ) (q₂ i)) M (symIcc N) f)) :
    δ ^ 2 * ((symIcc N).card : ℝ) ≤ kappa (I := I) s M * (pairSum (I := I) s M qH q₁ q₂ f).re := by
  have h1 := gauge_cs s M N qH q₁ q₂ δ f x₀ hM hδ hbd hsup h
  have h2 := gauge_sq_eq (I := I) s M qH q₁ q₂ f hfin
  have h2' : (↑(∑' y : ℤ, ‖gauge s M qH q₁ q₂ f y‖ ^ 2) : ℂ) =
      (kappa (I := I) s M : ℂ) * pairSum (I := I) s M qH q₁ q₂ f := by
    rw [h2]
    simp only [pairSum, kappa]
    push_cast
    ring
  have h3 : (∑' y : ℤ, ‖gauge s M qH q₁ q₂ f y‖ ^ 2) =
      kappa (I := I) s M * (pairSum (I := I) s M qH q₁ q₂ f).re := by
    have := congrArg Complex.re h2'
    simpa [Complex.ofReal_re, Complex.mul_re] using this
  exact le_trans h1 (le_of_eq h3)

/-! ## 4. Step B: the raw split, the identification and the GCS bound -/

/-- **Step B, the inner identification.**  For fixed raw coordinates, the four-fold sum of the
doubled `Rest`-products is the (normalised) `mCubeSum` of the truncated corner family. -/
theorem stepB_inner {I : Type} (s M N : ℕ) (hM0 : 0 < M) (qH : I → ℤ)
    (q₁ q₂ : I → Fin s → ℤ) (f : ℤ → ℂ) (x₀ : ℤ)
    (hvan : ∀ x : ℤ, x ∉ (symIcc N).map (Equiv.addRight x₀).toEmbedding → f x = 0)
    (i₀ i₁ : I) (a₀ a₀' a₁ a₁' : Fin M) :
    (∑ k₀ : Fin s → Fin M × Fin M, ∑ k₀' : Fin s → Fin M × Fin M,
        ∑ k₁ : Fin s → Fin M × Fin M, ∑ k₁' : Fin s → Fin M × Fin M,
          pairObjRaw s M qH q₁ q₂ f ⟨0, hM0⟩ i₀ i₁ a₀ a₀' a₁ a₁' k₀ k₀' k₁ k₁')
      = ((symIcc N).card : ℂ) * ((Fintype.card (Fin M × Fin M) : ℂ) ^ (4 * s)) *
          cFunCube s M N qH q₁ q₂ f x₀ i₀ i₁ a₀ a₀' a₁ a₁' := by
  have hpt' : ∀ (k₀ k₀' k₁ k₁' : Fin s → Fin M × Fin M),
      pairObjRaw s M qH q₁ q₂ f ⟨0, hM0⟩ i₀ i₁ a₀ a₀' a₁ a₁' k₀ k₀' k₁ k₁'
        = ∑' y : ℤ,
            Rest (Fin.cons (rawIncr qH i₀ a₀ a₀')
                (fun j => pdir (q₁ i₀ j) (q₂ i₀ j) (k₀ j)
                  - pdir (q₁ i₀ j) (q₂ i₀ j) (k₀' j))) f y *
              star (Rest (Fin.cons (rawIncr qH i₁ a₁ a₁')
                (fun j => pdir (q₁ i₁ j) (q₂ i₁ j) (k₁ j)
                  - pdir (q₁ i₁ j) (q₂ i₁ j) (k₁' j))) f y) := by
    intro k₀ k₀' k₁ k₁'
    dsimp only [pairObjRaw]
    unfold pairObj
    rw [incr_cons_form' s M hM0 (qH i₀) (q₁ i₀) (q₂ i₀) a₀ a₀' k₀ k₀',
      incr_cons_form' s M hM0 (qH i₁) (q₁ i₁) (q₂ i₁) a₁ a₁' k₁ k₁']
    rfl
  have hcongr : (∑ k₀ : Fin s → Fin M × Fin M, ∑ k₀' : Fin s → Fin M × Fin M,
        ∑ k₁ : Fin s → Fin M × Fin M, ∑ k₁' : Fin s → Fin M × Fin M,
          pairObjRaw s M qH q₁ q₂ f ⟨0, hM0⟩ i₀ i₁ a₀ a₀' a₁ a₁' k₀ k₀' k₁ k₁')
      = (∑ k₀ : Fin s → Fin M × Fin M, ∑ k₀' : Fin s → Fin M × Fin M,
        ∑ k₁ : Fin s → Fin M × Fin M, ∑ k₁' : Fin s → Fin M × Fin M,
          ∑' y : ℤ,
            Rest (Fin.cons (rawIncr qH i₀ a₀ a₀')
                (fun j => pdir (q₁ i₀ j) (q₂ i₀ j) (k₀ j)
                  - pdir (q₁ i₀ j) (q₂ i₀ j) (k₀' j))) f y *
              star (Rest (Fin.cons (rawIncr qH i₁ a₁ a₁')
                (fun j => pdir (q₁ i₁ j) (q₂ i₁ j) (k₁ j)
                  - pdir (q₁ i₁ j) (q₂ i₁ j) (k₁' j))) f y)) := by
    refine Finset.sum_congr rfl fun k₀ _ => ?_
    refine Finset.sum_congr rfl fun k₀' _ => ?_
    refine Finset.sum_congr rfl fun k₁ _ => ?_
    refine Finset.sum_congr rfl fun k₁' _ => ?_
    exact hpt' k₀ k₀' k₁ k₁'
  rw [hcongr]
  exact concatIdentSumI (s := s) (M := M) (N := N) (q₁ i₀) (q₂ i₀) (q₁ i₁) (q₂ i₁)
    (rawIncr qH i₀ a₀ a₀') (rawIncr qH i₁ a₁ a₁') f x₀ hvan

/-- **Step B, the pointwise GCS bound.** -/
theorem stepB_pt {I : Type} (s M N : ℕ) (hs : 1 ≤ s) (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ)
    (f : ℤ → ℂ) (x₀ : ℤ) (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1)
    (hvan : ∀ x : ℤ, x ∉ (symIcc N).map (Equiv.addRight x₀).toEmbedding → f x = 0)
    (i₀ i₁ : I) (a₀ a₀' a₁ a₁' : Fin M) :
    (cFunCube s M N qH q₁ q₂ f x₀ i₀ i₁ a₀ a₀' a₁ a₁').re
      ≤ 3 * (Zm s M N qH q₁ q₂ f i₀ i₁ a₀ a₀' a₁ a₁') ^ (1 / (2 : ℝ) ^ (2 * s)) := by
  refine le_trans (Complex.re_le_norm _) ?_
  exact cFunICubeLe s M N hs (q₁ i₀) (q₂ i₀) (q₁ i₁) (q₂ i₁)
    (rawIncr qH i₀ a₀ a₀') (rawIncr qH i₁ a₁ a₁') f x₀ hbd hvan

/-- **Step B.**  The doubled `Rest`-product is bounded by `κ⁻¹` times the normalised average of
the box powers `Zm`. -/
theorem stepB {I : Type} [Fintype I] [Nonempty I] (s M N : ℕ) (hM : 1 ≤ M) (hs : 1 ≤ s)
    (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ) (f : ℤ → ℂ) (x₀ : ℤ) (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1)
    (hvan : ∀ x : ℤ, x ∉ (symIcc N).map (Equiv.addRight x₀).toEmbedding → f x = 0) :
    (pairSum (I := I) s M qH q₁ q₂ f).re ≤ (kappa (I := I) s M)⁻¹ *
      (3 * ((symIcc N).card : ℝ) * ZmAvg s M N qH q₁ q₂ f) := by
  classical
  have hM0 : 0 < M := lt_of_lt_of_le Nat.zero_lt_one hM
  -- the raw split expands `pairSum` as the (frozen) four-fold sum
  have hsplit := pairObjRawSplit (I := I) s M hM0 qH q₁ q₂ f
  have hsplit' : pairSum (I := I) s M qH q₁ q₂ f =
      (M : ℂ) ^ 4 * pairObjRawSum s M ⟨0, hM0⟩ qH q₁ q₂ f := by
    dsimp only [pairSum, pairObjRawSum, pairObjRaw]
    exact hsplit
  -- rescale and bound each inner sum
  have hmain : (pairSum (I := I) s M qH q₁ q₂ f).re ≤
      (M : ℝ) ^ 4 * (((symIcc N).card : ℝ) *
        (((Fintype.card (Fin M × Fin M) : ℝ) ^ (4 * s)) * (3 * ZmPowSum s M N qH q₁ q₂ f))) := by
    rw [hsplit']
    have hmulre : (((M : ℂ) ^ 4 * pairObjRawSum s M ⟨0, hM0⟩ qH q₁ q₂ f)).re
        = (M : ℝ) ^ 4 * (pairObjRawSum s M ⟨0, hM0⟩ qH q₁ q₂ f).re :=
      re_natCast_pow_mul M 4 _
    rw [hmulre]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (show (0 : ℝ) ≤ (M : ℝ) from Nat.cast_nonneg M) 4)
    -- expand the frozen sum, bound each of the six levels by the pointwise bound
    have hstep1 : (pairObjRawSum s M ⟨0, hM0⟩ qH q₁ q₂ f).re ≤
        (∑ i₀ : I, ∑ i₁ : I, ∑ a₀ : Fin M, ∑ a₀' : Fin M, ∑ a₁ : Fin M, ∑ a₁' : Fin M,
          ((symIcc N).card : ℝ) * ((Fintype.card (Fin M × Fin M) : ℝ) ^ (4 * s)) *
            3 * (Zm s M N qH q₁ q₂ f i₀ i₁ a₀ a₀' a₁ a₁') ^ (1 / (2 : ℝ) ^ (2 * s))) := by
      rw [pairObjRawSum_eq, Complex.re_sum]
      refine Finset.sum_le_sum fun i₀ _ => ?_
      rw [Complex.re_sum]
      refine Finset.sum_le_sum fun i₁ _ => ?_
      rw [Complex.re_sum]
      refine Finset.sum_le_sum fun a₀ _ => ?_
      rw [Complex.re_sum]
      refine Finset.sum_le_sum fun a₀' _ => ?_
      rw [Complex.re_sum]
      refine Finset.sum_le_sum fun a₁ _ => ?_
      rw [Complex.re_sum]
      refine Finset.sum_le_sum fun a₁' _ => ?_
      rw [stepB_inner s M N hM0 qH q₁ q₂ f x₀ hvan i₀ i₁ a₀ a₀' a₁ a₁',
        re_natCast_mul_natCast_pow_mul]
      have hSnn : (0 : ℝ) ≤ ((symIcc N).card : ℝ) := Nat.cast_nonneg _
      have hXnn : (0 : ℝ) ≤ ((Fintype.card (Fin M × Fin M) : ℝ) ^ (4 * s)) :=
        pow_nonneg (Nat.cast_nonneg _) _
      calc ((symIcc N).card : ℝ) * ((Fintype.card (Fin M × Fin M) : ℝ) ^ (4 * s)) *
            (cFunCube s M N qH q₁ q₂ f x₀ i₀ i₁ a₀ a₀' a₁ a₁').re
          ≤ ((symIcc N).card : ℝ) * ((Fintype.card (Fin M × Fin M) : ℝ) ^ (4 * s)) *
              (3 * (Zm s M N qH q₁ q₂ f i₀ i₁ a₀ a₀' a₁ a₁') ^ (1 / (2 : ℝ) ^ (2 * s))) :=
            mul_le_mul_of_nonneg_left
              (stepB_pt s M N hs qH q₁ q₂ f x₀ hbd hvan i₀ i₁ a₀ a₀' a₁ a₁')
              (mul_nonneg hSnn hXnn)
        _ = ((symIcc N).card : ℝ) * ((Fintype.card (Fin M × Fin M) : ℝ) ^ (4 * s)) *
              3 * (Zm s M N qH q₁ q₂ f i₀ i₁ a₀ a₀' a₁ a₁') ^ (1 / (2 : ℝ) ^ (2 * s)) := by
            ac_rfl
    calc (pairObjRawSum s M ⟨0, hM0⟩ qH q₁ q₂ f).re
        ≤ (∑ i₀ : I, ∑ i₁ : I, ∑ a₀ : Fin M, ∑ a₀' : Fin M, ∑ a₁ : Fin M, ∑ a₁' : Fin M,
          ((symIcc N).card : ℝ) * ((Fintype.card (Fin M × Fin M) : ℝ) ^ (4 * s)) *
            3 * (Zm s M N qH q₁ q₂ f i₀ i₁ a₀ a₀' a₁ a₁') ^ (1 / (2 : ℝ) ^ (2 * s))) := hstep1
      _ = ((symIcc N).card : ℝ) * (((Fintype.card (Fin M × Fin M) : ℝ) ^ (4 * s)) *
            (3 * ZmPowSum s M N qH q₁ q₂ f)) := by
          rw [ZmPowSum_eq]
          simp only [← Finset.mul_sum]
          ring
  -- the average conversion and the arithmetic
  have hZmSum : ZmPowSum s M N qH q₁ q₂ f =
      (Fintype.card (I × I × Fin M × Fin M × Fin M × Fin M) : ℝ) * ZmAvg s M N qH q₁ q₂ f := by
    have h1 : ZmPowSum s M N qH q₁ q₂ f =
        ∑ j : I × I × Fin M × Fin M × Fin M × Fin M,
          (Zm6 s M N qH q₁ q₂ f j) ^ (1 / (2 : ℝ) ^ (2 * s)) := by
      rw [ZmPowSum, ← sumJ_eq (F := fun i j a b c d =>
        (Zm s M N qH q₁ q₂ f i j a b c d) ^ (1 / (2 : ℝ) ^ (2 * s)))]
      simp only [Zm6]
    rw [h1, ZmAvg, avg]
    have hne : ((Fintype.card (I × I × Fin M × Fin M × Fin M × Fin M) : ℝ)) ≠ 0 := by
      rw [cardJ_eq]
      have h1 : (0 : ℝ) < (Fintype.card I : ℝ) := by
        have hpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ‹Nonempty I›
        exact_mod_cast hpos
      have h2 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM0
      positivity
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  have hK : (M : ℝ) ^ 4 * ((Fintype.card (Fin M × Fin M) : ℝ) ^ (4 * s)) *
      ((Fintype.card (I × I × Fin M × Fin M × Fin M × Fin M) : ℝ)) = (kappa (I := I) s M)⁻¹ := by
    have hC := kappaArith (I := I) (s := s) (M := M) hM
    have hC' : kappa (I := I) s M * ((M : ℝ) ^ 4 *
        ((Fintype.card (Fin M × Fin M) : ℝ) ^ (4 * s)) *
        ((Fintype.card (I × I × Fin M × Fin M × Fin M × Fin M) : ℝ))) = 1 := by
      rw [← hC]
      ac_rfl
    exact (inv_eq_of_mul_eq_one_right hC').symm
  calc (pairSum (I := I) s M qH q₁ q₂ f).re
      ≤ (M : ℝ) ^ 4 * (((symIcc N).card : ℝ) *
          (((Fintype.card (Fin M × Fin M) : ℝ) ^ (4 * s)) * (3 * ZmPowSum s M N qH q₁ q₂ f))) := hmain
    _ = (kappa (I := I) s M)⁻¹ *
        (3 * ((symIcc N).card : ℝ) * ZmAvg s M N qH q₁ q₂ f) := by
        rw [hZmSum, ← hK]
        ac_rfl

/-- **The expansion.**  Steps A, B and C: the node's hypothesis implies
`δ²|S| ≤ 3|S| · ZmAvg`. -/
theorem expansion {I : Type} [Fintype I] [Nonempty I] (s M N : ℕ) (hM : 1 ≤ M) (hs : 1 ≤ s)
    (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ) (δ : ℝ) (f : ℤ → ℂ) (x₀ : ℤ) (hδ : 0 < δ)
    (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1) (hsup : ∀ x : ℤ, (N : ℤ) < |x - x₀| → f x = 0)
    (hfin : FinSuppZ f)
    (h : δ ≤ avg (fun i : I =>
        pbox (s + 1) (Fin.cons (qH i) (q₁ i)) (Fin.cons (0 : ℤ) (q₂ i)) M (symIcc N) f)) :
    δ ^ 2 * ((symIcc N).card : ℝ)
      ≤ 3 * ((symIcc N).card : ℝ) * ZmAvg s M N qH q₁ q₂ f := by
  have hA := stepA s M N qH q₁ q₂ δ f x₀ hM hδ hbd hsup hfin h
  have hB := stepB s M N hM hs qH q₁ q₂ f x₀ hbd (vanishes_off_translate (N := N) hsup)
  have hκpos := kappa_pos (I := I) (s := s) (M := M) hM
  have hκne : kappa (I := I) s M ≠ 0 := ne_of_gt hκpos
  calc δ ^ 2 * ((symIcc N).card : ℝ)
      ≤ kappa (I := I) s M * (pairSum (I := I) s M qH q₁ q₂ f).re := hA
    _ ≤ kappa (I := I) s M * ((kappa (I := I) s M)⁻¹ *
        (3 * ((symIcc N).card : ℝ) * ZmAvg s M N qH q₁ q₂ f)) :=
        mul_le_mul_of_nonneg_left hB (le_of_lt hκpos)
    _ = 3 * ((symIcc N).card : ℝ) * ZmAvg s M N qH q₁ q₂ f := by
        rw [← mul_assoc, mul_inv_cancel₀ hκne, one_mul]

end

end Work.Peluse.SwapC
