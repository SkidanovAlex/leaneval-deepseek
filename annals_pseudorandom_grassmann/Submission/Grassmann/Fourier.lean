import Mathlib

/-!
# Fourier analysis on spaces of matrices over `𝔽₂`

This file begins the "level"/rank Fourier analysis used by the Khot--Minzer--Safra
machinery, in particular by the Barak--Kothari--Steurer reduction of the Grassmann
Expansion Hypothesis to a small-set expansion theorem for the *shortcode graph* `L(V,W)`
(see arXiv:2209.04243).

For `A : Matrix (Fin m) (Fin n) 𝔽₂` (a linear map `𝔽₂ⁿ → 𝔽₂ᵐ`) and a dual matrix
`X : Matrix (Fin n) (Fin m) 𝔽₂` we define the character

  `mchar X A = ∏ i j, stdAddChar (X j i * A i j)`,

i.e. `mchar X A = (-1)^{Tr (X A)}`.  We prove that these characters are orthogonal,

  `∑ A, mchar X A * mchar Y A = (if X = Y then 2 ^ (m * n) else 0)`

(the *level* of a character being the rank of `X`), the dual orthogonality, and
Parseval's identity for the associated Fourier transform (`fhat`, `levelWeight`).
-/

open Matrix Finset BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

open AddChar

/-- The base character sum over `𝔽₂`: `∑_{x ∈ 𝔽₂} ψ (x * b)` is `2` for `b = 0` and `0`
otherwise (for `ψ` a nontrivial additive character). -/
lemma sum_stdAddChar_mul_two (b : ZMod 2) :
    ∑ x : ZMod 2, ZMod.stdAddChar (x * b) = if b = 0 then (2 : ℂ) else 0 := by
  rw [AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar 2)]
  norm_num

/-- `∏ i, (if f i = 0 then c else 0)` is `c ^ #ι` if `f = 0` and `0` otherwise. -/
lemma prod_ite_zero {ι : Type*} [Fintype ι] {M : ι → Type*} [∀ i, Zero (M i)]
    [∀ i, DecidableEq (M i)] (c : ℂ) (f : ∀ i, M i) :
    ∏ i, (if f i = 0 then c else 0) = if f = 0 then c ^ Fintype.card ι else 0 := by
  classical
  by_cases h : f = 0
  · subst h
    simp [Finset.prod_const]
  · obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact h (funext hc)
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Fubini for a product of sums over a dependent product type. -/
lemma sum_prod_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] (f : ∀ i, κ i → ℂ) :
    ∑ g : (∀ i, κ i), ∏ i, f i (g i) = ∏ i, ∑ a, f i a := by
  classical
  rw [Finset.prod_univ_sum (fun i => (Finset.univ : Finset (κ i))) f]
  simp

/-- The character of the additive group of `m × n` matrices over `𝔽₂` indexed by a dual
matrix `X : Matrix (Fin n) (Fin m) 𝔽₂`: `mchar X A = (-1) ^ (Tr (X A))`. -/
def mchar {m n : ℕ} (X : Matrix (Fin n) (Fin m) (ZMod 2))
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) : ℂ :=
  ∏ i : Fin m, ∏ j : Fin n, ZMod.stdAddChar (X j i * A i j)

lemma mchar_add_right {m n : ℕ} (X : Matrix (Fin n) (Fin m) (ZMod 2))
    (A B : Matrix (Fin m) (Fin n) (ZMod 2)) :
    mchar X (A + B) = mchar X A * mchar X B := by
  simp only [mchar, Matrix.add_apply, mul_add]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [AddChar.map_add_eq_mul]

lemma mchar_mul {m n : ℕ} (X Y : Matrix (Fin n) (Fin m) (ZMod 2))
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    mchar X A * mchar Y A = mchar (X + Y) A := by
  simp only [mchar, Matrix.add_apply, add_mul]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [AddChar.map_add_eq_mul]

lemma mchar_sum_eq {m n : ℕ} (X : Matrix (Fin n) (Fin m) (ZMod 2)) :
    ∑ A : Matrix (Fin m) (Fin n) (ZMod 2), mchar X A =
      if X = 0 then (2 : ℂ) ^ (m * n) else 0 := by
  classical
  have h1 : ∀ i : Fin m,
      (∏ j : Fin n, (∑ a : ZMod 2, ZMod.stdAddChar (X j i * a))) =
        if (fun j : Fin n => X j i) = 0 then (2 : ℂ) ^ n else 0 := by
    intro i
    have hstep : ∀ j : Fin n,
        (∑ a : ZMod 2, ZMod.stdAddChar (X j i * a)) =
          (if X j i = 0 then (2 : ℂ) else 0) := by
      intro j
      rw [← sum_stdAddChar_mul_two (X j i)]
      exact Finset.sum_congr rfl (fun a _ => by rw [mul_comm])
    rw [Finset.prod_congr rfl (fun j _ => hstep j)]
    rw [prod_ite_zero (2 : ℂ) (fun j : Fin n => X j i), Fintype.card_fin]
  have h2 : (∑ A : Matrix (Fin m) (Fin n) (ZMod 2), mchar X A) =
      ∏ i : Fin m, (∏ j : Fin n, (∑ a : ZMod 2, ZMod.stdAddChar (X j i * a))) := by
    rw [show (∑ A : Matrix (Fin m) (Fin n) (ZMod 2), mchar X A) =
        ∑ g : Fin m → Fin n → ZMod 2, ∏ i : Fin m, ∏ j : Fin n,
          ZMod.stdAddChar (X j i * g i j) from rfl]
    rw [sum_prod_pi (fun i (h : Fin n → ZMod 2) =>
      ∏ j : Fin n, ZMod.stdAddChar (X j i * h j))]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [sum_prod_pi (fun j (a : ZMod 2) => ZMod.stdAddChar (X j i * a))]
  rw [h2, Finset.prod_congr rfl (fun i _ => h1 i)]
  rw [prod_ite_zero ((2 : ℂ) ^ n) (fun i : Fin m => fun j : Fin n => X j i), Fintype.card_fin]
  by_cases hX : X = 0
  · have htr0 : (fun i : Fin m => fun j : Fin n => X j i) = 0 := by
      ext i j
      rw [hX]
      rfl
    rw [if_pos htr0, if_pos hX, ← pow_mul, Nat.mul_comm n m]
  · have htr0 : (fun i : Fin m => fun j : Fin n => X j i) ≠ 0 := by
      intro hh
      exact hX (funext fun j => funext fun i => congrFun (congrFun hh i) j)
    rw [if_neg htr0, if_neg hX]

/-- The *dual* orthogonality: summing over the characters instead of over the group. -/
lemma mchar_sum_left {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    ∑ X : Matrix (Fin n) (Fin m) (ZMod 2), mchar X A =
      if A = 0 then (2 : ℂ) ^ (m * n) else 0 := by
  classical
  have h1 : ∀ j : Fin n,
      (∏ i : Fin m, (∑ a : ZMod 2, ZMod.stdAddChar (a * A i j))) =
        if (fun i : Fin m => A i j) = 0 then (2 : ℂ) ^ m else 0 := by
    intro j
    rw [Finset.prod_congr rfl (fun i _ => sum_stdAddChar_mul_two (A i j))]
    rw [prod_ite_zero (2 : ℂ) (fun i : Fin m => A i j), Fintype.card_fin]
  have h2 : (∑ X : Matrix (Fin n) (Fin m) (ZMod 2), mchar X A) =
      ∏ j : Fin n, (∏ i : Fin m, (∑ a : ZMod 2, ZMod.stdAddChar (a * A i j))) := by
    rw [show (∑ X : Matrix (Fin n) (Fin m) (ZMod 2), mchar X A) =
        ∑ g : Fin n → Fin m → ZMod 2, ∏ i : Fin m, ∏ j : Fin n,
          ZMod.stdAddChar (g j i * A i j) from rfl]
    rw [Finset.sum_congr rfl (fun g _ => Finset.prod_comm)]
    rw [sum_prod_pi (fun j (h : Fin m → ZMod 2) =>
      ∏ i : Fin m, ZMod.stdAddChar (h i * A i j))]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [sum_prod_pi (fun i (a : ZMod 2) => ZMod.stdAddChar (a * A i j))]
  rw [h2, Finset.prod_congr rfl (fun j _ => h1 j)]
  rw [prod_ite_zero ((2 : ℂ) ^ m) (fun j : Fin n => fun i : Fin m => A i j), Fintype.card_fin]
  by_cases hA : A = 0
  · have htr0 : (fun j : Fin n => fun i : Fin m => A i j) = 0 := by
      ext j i
      rw [hA]
      rfl
    rw [if_pos htr0, if_pos hA, ← pow_mul, Nat.mul_comm m n]
  · have htr0 : (fun j : Fin n => fun i : Fin m => A i j) ≠ 0 := by
      intro hh
      exact hA (funext fun i => funext fun j => congrFun (congrFun hh j) i)
    rw [if_neg htr0, if_neg hA]

/-- Orthogonality of the matrix characters. -/
theorem mchar_orthogonal {m n : ℕ} (X Y : Matrix (Fin n) (Fin m) (ZMod 2)) :
    ∑ A : Matrix (Fin m) (Fin n) (ZMod 2), mchar X A * mchar Y A =
      if X = Y then (2 : ℂ) ^ (m * n) else 0 := by
  have hxy : X + Y = 0 ↔ X = Y := by
    constructor
    · intro h
      have h1 : X = -Y := by rw [add_eq_zero_iff_eq_neg] at h; exact h
      rw [h1]
      ext i j
      exact CharTwo.neg_eq _
    · intro h
      rw [h]
      ext i j
      exact CharTwo.add_self_eq_zero _
  rw [Finset.sum_congr rfl (fun A _ => mchar_mul X Y A), mchar_sum_eq (X + Y)]
  by_cases h : X = Y
  · rw [if_pos (hxy.mpr h), if_pos h]
  · rw [if_neg (fun hh => h (hxy.mp hh)), if_neg h]

/-- The character `mchar X ·` has unit modulus. -/
lemma norm_mchar {m n : ℕ} (X : Matrix (Fin n) (Fin m) (ZMod 2))
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) : ‖mchar X A‖ = 1 := by
  rw [mchar, norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [norm_prod]
  exact Finset.prod_eq_one fun j _ => AddChar.norm_apply _ _

/-- The Fourier coefficient `f̂ X = ∑_A f A * mchar X A` of a function on `m × n`
matrices over `𝔽₂`. -/
def fhat {m n : ℕ} (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ)
    (X : Matrix (Fin n) (Fin m) (ZMod 2)) : ℂ :=
  ∑ A : Matrix (Fin m) (Fin n) (ZMod 2), f A * mchar X A

/-- The **level-`r` Fourier weight** of `f`: the sum of the squared moduli of the Fourier
coefficients supported on matrices `X` of rank `r`.  (The *level* of a character of
`L(𝔽₂ⁿ, 𝔽₂ᵐ)` is the rank of its indexing matrix; this is the degree used in the KMS /
Barak--Kothari--Steurer analysis of the shortcode graph.) -/
def levelWeight {m n : ℕ} (r : ℕ) (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) : ℝ :=
  ∑ X : Matrix (Fin n) (Fin m) (ZMod 2), if X.rank = r then ‖fhat f X‖ ^ 2 else 0

/-- **Parseval/Plancherel identity** for the matrix Fourier transform. -/
theorem fhat_parseval {m n : ℕ} (f g : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    ∑ X : Matrix (Fin n) (Fin m) (ZMod 2), fhat f X * fhat g X =
      (2 : ℂ) ^ (m * n) * ∑ A : Matrix (Fin m) (Fin n) (ZMod 2), f A * g A := by
  classical
  have hAB : ∀ A B : Matrix (Fin m) (Fin n) (ZMod 2), A + B = 0 ↔ B = A := by
    intro A B
    constructor
    · intro h
      have h1 : A = -B := (add_eq_zero_iff_eq_neg).mp h
      rw [h1]
      ext i j
      exact (CharTwo.neg_eq (B i j)).symm
    · intro h
      rw [h]
      ext i j
      exact CharTwo.add_self_eq_zero _
  have key : ∀ X : Matrix (Fin n) (Fin m) (ZMod 2),
      fhat f X * fhat g X =
        ∑ A : Matrix (Fin m) (Fin n) (ZMod 2), ∑ B : Matrix (Fin m) (Fin n) (ZMod 2),
          f A * g B * mchar X (A + B) := by
    intro X
    rw [fhat, fhat, Finset.sum_mul]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [mchar_add_right]
    ring
  calc ∑ X : Matrix (Fin n) (Fin m) (ZMod 2), fhat f X * fhat g X
      = ∑ X, ∑ A : Matrix (Fin m) (Fin n) (ZMod 2),
          ∑ B : Matrix (Fin m) (Fin n) (ZMod 2), f A * g B * mchar X (A + B) :=
        Finset.sum_congr rfl fun X _ => key X
    _ = ∑ A : Matrix (Fin m) (Fin n) (ZMod 2),
          ∑ B : Matrix (Fin m) (Fin n) (ZMod 2),
            ∑ X : Matrix (Fin n) (Fin m) (ZMod 2), f A * g B * mchar X (A + B) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun A _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ A : Matrix (Fin m) (Fin n) (ZMod 2), ∑ B : Matrix (Fin m) (Fin n) (ZMod 2),
          f A * g B * (∑ X : Matrix (Fin n) (Fin m) (ZMod 2), mchar X (A + B)) := by
        refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ A : Matrix (Fin m) (Fin n) (ZMod 2), ∑ B : Matrix (Fin m) (Fin n) (ZMod 2),
          f A * g B * (if A + B = 0 then (2 : ℂ) ^ (m * n) else 0) := by
        refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
        rw [mchar_sum_left]
    _ = ∑ A : Matrix (Fin m) (Fin n) (ZMod 2), (2 : ℂ) ^ (m * n) * (f A * g A) := by
        refine Finset.sum_congr rfl fun A _ => ?_
        have hstep : ∀ B : Matrix (Fin m) (Fin n) (ZMod 2),
            f A * g B * (if A + B = 0 then (2 : ℂ) ^ (m * n) else 0) =
              if B = A then (2 : ℂ) ^ (m * n) * (f A * g A) else 0 := by
          intro B
          by_cases h : B = A
          · rw [if_pos ((hAB A B).mpr h), if_pos h, h]
            ring
          · rw [if_neg (fun hh => h ((hAB A B).mp hh)), if_neg h]
            ring
        rw [Finset.sum_congr rfl (fun B _ => hstep B)]
        rw [Finset.sum_eq_single A (fun B _ hB => by rw [if_neg hB])
          (fun h => absurd (Finset.mem_univ A) h)]
        rw [if_pos rfl]
    _ = (2 : ℂ) ^ (m * n) * ∑ A : Matrix (Fin m) (Fin n) (ZMod 2), f A * g A := by
        rw [Finset.mul_sum]

/-- `mchar X ·` is symmetric in the second argument (matrix addition is commutative). -/
lemma mchar_mul_comm {m n : ℕ} (X : Matrix (Fin n) (Fin m) (ZMod 2))
    (A B : Matrix (Fin m) (Fin n) (ZMod 2)) :
    mchar X B * mchar X A = mchar X (A + B) := by
  rw [← mchar_add_right X B A, add_comm]

/-- **Fourier inversion** for functions on `m × n` matrices over `𝔽₂`. -/
theorem fhat_inversion {m n : ℕ} (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ)
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    ∑ X : Matrix (Fin n) (Fin m) (ZMod 2), fhat f X * mchar X A =
      (2 : ℂ) ^ (m * n) * f A := by
  classical
  have hAB : ∀ A B : Matrix (Fin m) (Fin n) (ZMod 2), A + B = 0 ↔ B = A := by
    intro A B
    constructor
    · intro h
      have h1 : A = -B := (add_eq_zero_iff_eq_neg).mp h
      rw [h1]
      ext i j
      exact (CharTwo.neg_eq (B i j)).symm
    · intro h
      rw [h]
      ext i j
      exact CharTwo.add_self_eq_zero _
  have key : ∀ X : Matrix (Fin n) (Fin m) (ZMod 2), fhat f X * mchar X A =
      ∑ B : Matrix (Fin m) (Fin n) (ZMod 2), f B * mchar X (A + B) := by
    intro X
    rw [fhat, Finset.sum_mul]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [mul_assoc, mchar_mul_comm]
  calc ∑ X : Matrix (Fin n) (Fin m) (ZMod 2), fhat f X * mchar X A
      = ∑ X, ∑ B : Matrix (Fin m) (Fin n) (ZMod 2), f B * mchar X (A + B) :=
        Finset.sum_congr rfl fun X _ => key X
    _ = ∑ B : Matrix (Fin m) (Fin n) (ZMod 2),
          ∑ X : Matrix (Fin n) (Fin m) (ZMod 2), f B * mchar X (A + B) :=
        Finset.sum_comm
    _ = ∑ B : Matrix (Fin m) (Fin n) (ZMod 2),
          f B * (∑ X : Matrix (Fin n) (Fin m) (ZMod 2), mchar X (A + B)) := by
        refine Finset.sum_congr rfl fun B _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ B : Matrix (Fin m) (Fin n) (ZMod 2),
          f B * (if A + B = 0 then (2 : ℂ) ^ (m * n) else 0) := by
        refine Finset.sum_congr rfl fun B _ => ?_
        rw [mchar_sum_left]
    _ = (2 : ℂ) ^ (m * n) * f A := by
        have hstep : ∀ B : Matrix (Fin m) (Fin n) (ZMod 2),
            f B * (if A + B = 0 then (2 : ℂ) ^ (m * n) else 0) =
              if B = A then (2 : ℂ) ^ (m * n) * f A else 0 := by
          intro B
          by_cases h : B = A
          · rw [if_pos ((hAB A B).mpr h), if_pos h, h]
            ring
          · rw [if_neg (fun hh => h ((hAB A B).mp hh)), if_neg h]
            ring
        rw [Finset.sum_congr rfl (fun B _ => hstep B),
          Finset.sum_eq_single A (fun B _ hB => by rw [if_neg hB])
            (fun h => absurd (Finset.mem_univ A) h), if_pos rfl]

/-! ## Real Parseval and the level decomposition -/

/-- `ZMod.stdAddChar` takes the values `±1`, hence is real. -/
lemma star_stdAddChar_zmod_two (t : ZMod 2) : star (ZMod.stdAddChar t) = ZMod.stdAddChar t := by
  rw [Complex.star_def,
    ← Complex.inv_eq_conj (AddChar.norm_apply (ZMod.stdAddChar (N := 2)) t),
    ← AddChar.map_neg_eq_inv]
  congr 1
  exact CharTwo.neg_eq t

/-- The character `mchar X ·` is real (it takes the values `±1`). -/
lemma star_mchar {m n : ℕ} (X : Matrix (Fin n) (Fin m) (ZMod 2))
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) : star (mchar X A) = mchar X A := by
  rw [mchar, star_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [star_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact star_stdAddChar_zmod_two _

/-- Taking the Fourier transform commutes with complex conjugation. -/
lemma fhat_star {m n : ℕ} (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ)
    (X : Matrix (Fin n) (Fin m) (ZMod 2)) :
    fhat (fun A => star (f A)) X = star (fhat f X) := by
  rw [fhat, fhat, star_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [star_mul, star_mchar]
  ring

/-- **Parseval's identity, real form**: `∑_X ‖f̂ X‖² = 2^{mn} ∑_A ‖f A‖²`. -/
theorem fhat_parseval_normSq {m n : ℕ} (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    ∑ X : Matrix (Fin n) (Fin m) (ZMod 2), ‖fhat f X‖ ^ 2 =
      (2 : ℝ) ^ (m * n) * ∑ A : Matrix (Fin m) (Fin n) (ZMod 2), ‖f A‖ ^ 2 := by
  have h := fhat_parseval f (fun A => star (f A))
  simp only [fhat_star] at h
  simp only [Complex.star_def, Complex.mul_conj] at h
  rw [← Complex.ofReal_sum] at h
  rw [← Complex.ofReal_sum] at h
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_num] at h
  rw [← Complex.ofReal_pow] at h
  rw [← Complex.ofReal_mul] at h
  have h' := Complex.ofReal_inj.mp h
  simpa only [Complex.normSq_eq_norm_sq] using h'

/-- Summing the level weights over all possible ranks gives the total Fourier weight. -/
theorem sum_levelWeight {m n : ℕ} (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    ∑ d ∈ Finset.range (min m n + 1), levelWeight d f =
      ∑ X : Matrix (Fin n) (Fin m) (ZMod 2), ‖fhat f X‖ ^ 2 := by
  classical
  have hrank : ∀ X : Matrix (Fin n) (Fin m) (ZMod 2), X.rank ≤ min m n := fun X =>
    le_min (Matrix.rank_le_width X) (Matrix.rank_le_height X)
  have hswap : (∑ d ∈ Finset.range (min m n + 1), levelWeight d f) =
      ∑ X : Matrix (Fin n) (Fin m) (ZMod 2),
        ∑ d ∈ Finset.range (min m n + 1),
          (if X.rank = d then ‖fhat f X‖ ^ 2 else 0) := by
    simp only [levelWeight]
    rw [Finset.sum_comm]
  rw [hswap]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [Finset.sum_eq_single X.rank (fun d _ hd => by rw [if_neg (Ne.symm hd)])
    (fun h => absurd (Finset.mem_range.mpr (by have := hrank X; omega)) h), if_pos rfl]

/-- **Level Parseval**: the sum of the level-`d` Fourier weights over all `d` is
`2^{mn}` times the squared `L²` norm of `f`. -/
theorem sum_levelWeight_eq {m n : ℕ} (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    ∑ d ∈ Finset.range (min m n + 1), levelWeight d f =
      (2 : ℝ) ^ (m * n) * ∑ A : Matrix (Fin m) (Fin n) (ZMod 2), ‖f A‖ ^ 2 := by
  rw [sum_levelWeight, fhat_parseval_normSq]

end

end Submission.Grassmann
