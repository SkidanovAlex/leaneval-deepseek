import Submission.Grassmann.Fourier
import Submission.Commons.LinearAlgebra.Matrix.rank_add_le

/-!
# The degree filtration on `L(V,W)` (`= matrices over `𝔽₂`)

This file develops, for functions `f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ` on the space of
linear maps (the "shortcode" space `L(V,W)` of the KMS / Barak--Kothari--Steurer analysis),
the *degree* theory of arXiv:2209.04243, Section 3.

The characters `mchar X` (for `X : Matrix (Fin n) (Fin m) 𝔽₂`) are indexed by the dual
space; the **level** of a character is the rank of `X`, and the **degree** of a function is
the maximal level occurring in its Fourier expansion.

Contents:

* linearity of the Fourier transform `fhat`;
* the level projections `projPure d f` (Fourier support of rank exactly `d`) and
  `projLe d f` (Fourier support of rank at most `d`), with `fhat_projPure`, `fhat_projLe`;
* the degree filtration: `DegLe d f` (Fourier support in ranks `≤ d`) as the `ℂ`-span of
  the characters of rank `≤ d`, its equivalence with the vanishing of the Fourier
  coefficients, and closure under addition/scalars;
* **`degLe_mul`**: the product of a function of degree `≤ d` and one of degree `≤ e` has
  degree `≤ d + e` -- the `L(V,W)` analogue of `mul_mem_Vup` on the Grassmann side,
  which is the structural heart of the degree calculus (the paper's Lemma 3.6/Lemma 3.7
  refinements rest on it).
-/

open Matrix Finset BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

/-! ## Subadditivity of the matrix rank (local copy of a Mathlib gap) -/

/-- Rank is subadditive: `rank (A + B) ≤ rank A + rank B`. (Also in the commons.) -/
lemma rank_add_le_zmod {m n : Type*} [Fintype m] [Fintype n] (A B : Matrix m n (ZMod 2)) :
    (A + B).rank ≤ A.rank + B.rank :=
  Commons.LinearAlgebra.Matrix.rank_add_le A B

/-! ## Linearity of the Fourier transform -/

lemma fhat_zero {m n : ℕ} (X : Matrix (Fin n) (Fin m) (ZMod 2)) :
    fhat (fun _ : Matrix (Fin m) (Fin n) (ZMod 2) => (0 : ℂ)) X = 0 := by
  simp [fhat]

lemma fhat_add {m n : ℕ} (f g : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ)
    (X : Matrix (Fin n) (Fin m) (ZMod 2)) :
    fhat (f + g) X = fhat f X + fhat g X := by
  rw [fhat, fhat, fhat, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun A _ => by rw [Pi.add_apply, add_mul]

lemma fhat_smul {m n : ℕ} (c : ℂ) (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ)
    (X : Matrix (Fin n) (Fin m) (ZMod 2)) :
    fhat (c • f) X = c * fhat f X := by
  rw [fhat, fhat, Finset.mul_sum]
  exact Finset.sum_congr rfl fun A _ => by rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

lemma fhat_neg {m n : ℕ} (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ)
    (X : Matrix (Fin n) (Fin m) (ZMod 2)) :
    fhat (-f) X = -fhat f X := by
  rw [fhat, fhat, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun A _ => by rw [Pi.neg_apply, neg_mul]

lemma fhat_sub {m n : ℕ} (f g : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ)
    (X : Matrix (Fin n) (Fin m) (ZMod 2)) :
    fhat (f - g) X = fhat f X - fhat g X := by
  rw [fhat, fhat, fhat, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun A _ => by rw [Pi.sub_apply, sub_mul]

lemma fhat_const {m n : ℕ} (c : ℂ) (X : Matrix (Fin n) (Fin m) (ZMod 2)) :
    fhat (fun _ : Matrix (Fin m) (Fin n) (ZMod 2) => c) X =
      (if X = 0 then c * (2 : ℂ) ^ (m * n) else 0) := by
  simp only [fhat]
  rw [← Finset.mul_sum, mchar_sum_eq]
  by_cases h : X = 0 <;> simp [h]

/-! ## The level projections -/

/-- The **rank-`d` (pure-degree-`d`) part** of `f`, as an (unnormalised) function:
the sum of the Fourier coefficients on characters of level exactly `d`. -/
def projPure {m n : ℕ} (d : ℕ) (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    Matrix (Fin m) (Fin n) (ZMod 2) → ℂ :=
  fun A => ∑ X : Matrix (Fin n) (Fin m) (ZMod 2),
    if X.rank = d then fhat f X * mchar X A else 0

/-- The **degree-`≤ d` part** of `f`, as an (unnormalised) function. -/
def projLe {m n : ℕ} (d : ℕ) (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    Matrix (Fin m) (Fin n) (ZMod 2) → ℂ :=
  fun A => ∑ X : Matrix (Fin n) (Fin m) (ZMod 2),
    if X.rank ≤ d then fhat f X * mchar X A else 0

/-- The Fourier transform of the pure-level-`d` projection. -/
theorem fhat_projPure {m n : ℕ} (d : ℕ) (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ)
    (X : Matrix (Fin n) (Fin m) (ZMod 2)) :
    fhat (projPure d f) X = (if X.rank = d then (2 : ℂ) ^ (m * n) else 0) * fhat f X := by
  have h1 : (∑ A : Matrix (Fin m) (Fin n) (ZMod 2), projPure d f A * mchar X A) =
      ∑ A : Matrix (Fin m) (Fin n) (ZMod 2),
        ∑ Y : Matrix (Fin n) (Fin m) (ZMod 2),
          (if Y.rank = d then fhat f Y * (mchar Y A * mchar X A) else 0) := by
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [projPure, Finset.sum_mul]
    refine Finset.sum_congr rfl fun Y _ => ?_
    by_cases hY : Y.rank = d <;> simp [hY, mul_assoc]
  have h2 : (∑ Y : Matrix (Fin n) (Fin m) (ZMod 2),
        ∑ A : Matrix (Fin m) (Fin n) (ZMod 2),
          (if Y.rank = d then fhat f Y * (mchar Y A * mchar X A) else 0)) =
      ∑ Y : Matrix (Fin n) (Fin m) (ZMod 2),
        (if Y.rank = d then fhat f Y * (if Y = X then (2 : ℂ) ^ (m * n) else 0) else 0) := by
    refine Finset.sum_congr rfl fun Y _ => ?_
    by_cases hY : Y.rank = d
    · simp only [if_pos hY]
      rw [← Finset.mul_sum, mchar_orthogonal Y X]
    · simp [if_neg hY]
  rw [fhat, h1, Finset.sum_comm, h2]
  by_cases hX : X.rank = d
  · rw [if_pos hX, Finset.sum_eq_single X]
    · simp [hX]; ring
    · intro Y _ hYX; simp [hYX]
    · intro h; exact absurd (Finset.mem_univ X) h
  · rw [if_neg hX, zero_mul]
    refine Finset.sum_eq_zero fun Y _ => ?_
    by_cases hYX : Y = X
    · rw [hYX]; simp [hX]
    · simp [hYX]

/-- The Fourier transform of the degree-`≤ d` projection. -/
theorem fhat_projLe {m n : ℕ} (d : ℕ) (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ)
    (X : Matrix (Fin n) (Fin m) (ZMod 2)) :
    fhat (projLe d f) X = (if X.rank ≤ d then (2 : ℂ) ^ (m * n) else 0) * fhat f X := by
  have h1 : (∑ A : Matrix (Fin m) (Fin n) (ZMod 2), projLe d f A * mchar X A) =
      ∑ A : Matrix (Fin m) (Fin n) (ZMod 2),
        ∑ Y : Matrix (Fin n) (Fin m) (ZMod 2),
          (if Y.rank ≤ d then fhat f Y * (mchar Y A * mchar X A) else 0) := by
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [projLe, Finset.sum_mul]
    refine Finset.sum_congr rfl fun Y _ => ?_
    by_cases hY : Y.rank ≤ d <;> simp [hY, mul_assoc]
  have h2 : (∑ Y : Matrix (Fin n) (Fin m) (ZMod 2),
        ∑ A : Matrix (Fin m) (Fin n) (ZMod 2),
          (if Y.rank ≤ d then fhat f Y * (mchar Y A * mchar X A) else 0)) =
      ∑ Y : Matrix (Fin n) (Fin m) (ZMod 2),
        (if Y.rank ≤ d then fhat f Y * (if Y = X then (2 : ℂ) ^ (m * n) else 0) else 0) := by
    refine Finset.sum_congr rfl fun Y _ => ?_
    by_cases hY : Y.rank ≤ d
    · simp only [if_pos hY]
      rw [← Finset.mul_sum, mchar_orthogonal Y X]
    · simp [if_neg hY]
  rw [fhat, h1, Finset.sum_comm, h2]
  by_cases hX : X.rank ≤ d
  · rw [if_pos hX, Finset.sum_eq_single X]
    · simp [hX]; ring
    · intro Y _ hYX; simp [hYX]
    · intro h; exact absurd (Finset.mem_univ X) h
  · rw [if_neg hX, zero_mul]
    refine Finset.sum_eq_zero fun Y _ => ?_
    by_cases hYX : Y = X
    · rw [hYX]; simp [hX]
    · simp [hYX]


/-! ## The degree filtration -/

/-- The space of functions on `L(V,W)` whose Fourier support lies in characters of
rank at most `d`: the `ℂ`-span of the characters `mchar X` with `X.rank ≤ d`. -/
def charLe {m n : ℕ} (d : ℕ) : Submodule ℂ (Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :=
  Submodule.span ℂ {f | ∃ X : Matrix (Fin n) (Fin m) (ZMod 2), X.rank ≤ d ∧ f = mchar X}

/-- `f` has **degree at most `d`**: its Fourier support is contained in the characters of
level (rank) at most `d`. -/
def DegLe {m n : ℕ} (d : ℕ) (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) : Prop :=
  ∀ X : Matrix (Fin n) (Fin m) (ZMod 2), d < X.rank → fhat f X = 0

lemma mchar_mem_charLe {m n d : ℕ} {X : Matrix (Fin n) (Fin m) (ZMod 2)}
    (hX : X.rank ≤ d) : (mchar X) ∈ charLe (m := m) (n := n) d :=
  Submodule.subset_span ⟨X, hX, rfl⟩

/-- The product of two characters is a character: `mchar X * mchar Y = mchar (X + Y)`. -/
lemma mchar_mul_fun {m n : ℕ} (X Y : Matrix (Fin n) (Fin m) (ZMod 2)) :
    (mchar X) * (mchar Y) = (mchar (X + Y) : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) := by
  funext A
  exact mchar_mul X Y A

lemma degLe_zero {m n d : ℕ} : DegLe (m := m) (n := n) d (fun _ => (0 : ℂ)) :=
  fun X _ => fhat_zero X

lemma degLe_add {m n d : ℕ} {f g : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ}
    (hf : DegLe d f) (hg : DegLe d g) : DegLe d (f + g) := by
  intro X hX
  rw [fhat_add f g X, hf X hX, hg X hX, add_zero]

lemma degLe_neg {m n d : ℕ} {f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ}
    (hf : DegLe d f) : DegLe d (-f) := by
  intro X hX
  rw [fhat_neg f X, hf X hX, neg_zero]

lemma degLe_sub {m n d : ℕ} {f g : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ}
    (hf : DegLe d f) (hg : DegLe d g) : DegLe d (f - g) := by
  intro X hX
  rw [fhat_sub f g X, hf X hX, hg X hX, sub_zero]

lemma degLe_smul {m n d : ℕ} (c : ℂ) {f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ}
    (hf : DegLe d f) : DegLe d (c • f) := by
  intro X hX
  rw [fhat_smul c f X, hf X hX, mul_zero]

lemma degLe_mono {m n d e : ℕ} {f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ}
    (hde : d ≤ e) (hf : DegLe d f) : DegLe e f :=
  fun X hX => hf X (lt_of_le_of_lt hde hX)

/-- A single character has degree at most its rank. -/
lemma degLe_mchar {m n d : ℕ} {X : Matrix (Fin n) (Fin m) (ZMod 2)} (hX : X.rank ≤ d) :
    DegLe d (mchar X) := by
  intro Z hZ
  have h : fhat (mchar X) Z = (if X = Z then (2 : ℂ) ^ (m * n) else 0) := by
    rw [fhat]; exact mchar_orthogonal X Z
  rw [h, if_neg]
  intro hXZ
  rw [hXZ] at hX
  exact absurd hX (not_le.mpr hZ)

/-- Members of the level-`d` span have degree at most `d`. -/
lemma degLe_of_mem_charLe {m n d : ℕ} {f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ}
    (hf : f ∈ charLe (m := m) (n := n) d) : DegLe d f := by
  refine Submodule.span_induction (p := fun f _ => DegLe d f) ?_ ?_ ?_ ?_ hf
  · rintro f ⟨X, hX, rfl⟩
    exact degLe_mchar hX
  · exact degLe_zero
  · intro a b _ _ ha hb
    exact degLe_add ha hb
  · intro c a _ ha
    exact degLe_smul c ha

/-- **Multiplication of characters**: `charLe d · charLe e ⊆ charLe (d + e)`. -/
lemma charLe_mul_mem {m n d e : ℕ} {f g : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ}
    (hf : f ∈ charLe (m := m) (n := n) d) (hg : g ∈ charLe (m := m) (n := n) e) :
    f * g ∈ charLe (m := m) (n := n) (d + e) := by
  have hchar : ∀ (X : Matrix (Fin n) (Fin m) (ZMod 2)), X.rank ≤ d →
      ∀ g : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ,
        g ∈ charLe (m := m) (n := n) e →
          (mchar X) * g ∈ charLe (m := m) (n := n) (d + e) := by
    intro X hX g hg
    refine Submodule.span_induction
      (p := fun g _ => (mchar X) * g ∈ charLe (m := m) (n := n) (d + e)) ?_ ?_ ?_ ?_ hg
    · rintro g ⟨Y, hY, rfl⟩
      rw [mchar_mul_fun]
      exact mchar_mem_charLe (le_trans (rank_add_le_zmod X Y) (add_le_add hX hY))
    · simp
    · intro a b _ _ ha hb
      rw [mul_add]; exact Submodule.add_mem _ ha hb
    · intro c a _ ha
      have h : (mchar X) * (c • a) = c • ((mchar X) * a) := by
        funext A; simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [h]; exact Submodule.smul_mem _ c ha
  refine (Submodule.span_induction
    (p := fun f _ => ∀ g ∈ charLe (m := m) (n := n) e,
      f * g ∈ charLe (m := m) (n := n) (d + e)) ?_ ?_ ?_ ?_ hf) g hg
  · rintro f ⟨X, hX, rfl⟩
    exact hchar X hX
  · intro g _; simp
  · intro a b _ _ ha hb g hg
    rw [add_mul]; exact Submodule.add_mem _ (ha g hg) (hb g hg)
  · intro c a _ ha g hg
    have h : (c • a) * g = c • (a * g) := by
      funext A; simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [h]; exact Submodule.smul_mem _ c (ha g hg)

/-- The `projLe d f` is a sum of characters of rank at most `d`. -/
lemma projLe_eq_sum {m n : ℕ} (d : ℕ) (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    projLe d f = ∑ X : Matrix (Fin n) (Fin m) (ZMod 2),
      (if X.rank ≤ d then fhat f X else 0) • (mchar X) := by
  funext A
  rw [projLe, Finset.sum_apply]
  refine Finset.sum_congr rfl fun X _ => ?_
  by_cases hX : X.rank ≤ d <;> simp [hX]

lemma projLe_mem_charLe {m n : ℕ} (d : ℕ) (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    projLe d f ∈ charLe (m := m) (n := n) d := by
  rw [projLe_eq_sum]
  refine Submodule.sum_mem _ fun X _ => ?_
  by_cases hX : X.rank ≤ d
  · exact Submodule.smul_mem _ _ (mchar_mem_charLe hX)
  · simp [hX]

/-- If `f` has degree at most `d` then the degree-`≤d` projection is `2^{mn} f`. -/
lemma projLe_eq_smul {m n : ℕ} {d : ℕ} {f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ}
    (hf : DegLe d f) : projLe d f = (2 : ℂ) ^ (m * n) • f := by
  funext A
  rw [projLe, Pi.smul_apply, smul_eq_mul, ← fhat_inversion f A]
  refine Finset.sum_congr rfl fun X _ => ?_
  by_cases hX : X.rank ≤ d
  · simp [hX]
  · rw [if_neg hX, hf X (Nat.lt_of_not_le hX), zero_mul]

/-- A function of degree at most `d` lies in the level-`d` span. -/
lemma mem_charLe_of_degLe {m n d : ℕ} {f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ}
    (hf : DegLe d f) : f ∈ charLe (m := m) (n := n) d := by
  have h1 : projLe d f ∈ charLe (m := m) (n := n) d := projLe_mem_charLe d f
  rw [projLe_eq_smul hf] at h1
  have h2 : ((2 : ℂ) ^ (m * n))⁻¹ • ((2 : ℂ) ^ (m * n) • f) ∈ charLe (m := m) (n := n) d :=
    Submodule.smul_mem _ _ h1
  rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)), one_smul] at h2

/-- **The degree filtration in terms of Fourier support.** -/
theorem degLe_iff_mem_charLe {m n d : ℕ} {f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ} :
    DegLe d f ↔ f ∈ charLe (m := m) (n := n) d :=
  ⟨mem_charLe_of_degLe, degLe_of_mem_charLe⟩

/-- **Degree is subadditive under multiplication**: the product of a function of degree
at most `d` and one of degree at most `e` has degree at most `d + e`.  This is the
`L(V,W)` analogue of `mul_mem_Vup` on the Grassmann side. -/
theorem degLe_mul {m n : ℕ} {d e : ℕ} {f g : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ}
    (hf : DegLe d f) (hg : DegLe e g) : DegLe (d + e) (f * g) :=
  degLe_of_mem_charLe
    (charLe_mul_mem (mem_charLe_of_degLe hf) (mem_charLe_of_degLe hg))

/-- A constant function has degree `0`. -/
lemma degLe_const {m n : ℕ} (c : ℂ) :
    DegLe (m := m) (n := n) 0 (fun _ : Matrix (Fin m) (Fin n) (ZMod 2) => c) := by
  have h0 : (mchar (0 : Matrix (Fin n) (Fin m) (ZMod 2))) ∈ charLe (m := m) (n := n) 0 :=
    mchar_mem_charLe (by rw [Matrix.rank_zero])
  have hmem : ((fun _ : Matrix (Fin m) (Fin n) (ZMod 2) => c)) ∈ charLe (m := m) (n := n) 0 := by
    have : (fun _ : Matrix (Fin m) (Fin n) (ZMod 2) => c) = c • (mchar (0 : Matrix (Fin n) (Fin m) (ZMod 2))) := by
      funext A
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mchar, Finset.prod_eq_one (fun i _ => Finset.prod_eq_one (fun j _ => by simp))]
      ring
    rw [this]
    exact Submodule.smul_mem _ _ h0
  exact degLe_of_mem_charLe hmem

/-- **The degree filtration in terms of level weights.** -/
theorem degLe_iff_levelWeight {m n : ℕ} {d : ℕ} {f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ} :
    DegLe d f ↔ ∀ e, d < e → levelWeight (m := m) (n := n) e f = 0 := by
  constructor
  · intro hf e he
    refine Finset.sum_eq_zero fun X _ => ?_
    by_cases hX : X.rank = e
    · rw [if_pos hX, hf X (by rw [hX]; exact he)]; norm_num
    · simp [hX]
  · intro h X hX
    have hle : ‖fhat f X‖ ^ 2 ≤ levelWeight (m := m) (n := n) X.rank f := by
      rw [levelWeight]
      have := Finset.single_le_sum
        (f := fun Y : Matrix (Fin n) (Fin m) (ZMod 2) =>
          if Y.rank = X.rank then ‖fhat f Y‖ ^ 2 else 0)
        (fun Y _ => by by_cases hY : Y.rank = X.rank <;> simp [hY])
        (Finset.mem_univ X)
      simpa using this
    rw [h X.rank hX] at hle
    have hz : ‖fhat f X‖ ^ 2 = 0 := le_antisymm hle (by positivity)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

end

end Submission.Grassmann
