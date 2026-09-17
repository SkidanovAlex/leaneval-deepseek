import Mathlib
import Submission.Commons.Algebra.Lie.e8_finrank
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_isKilling
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_norm_two_conj_simple
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_diag_offdiag_symm

namespace Commons.Algebra.Lie.SerreConstruction

open Commons.Algebra.Lie
open scoped BigOperators
open Matrix

noncomputable section

set_option maxHeartbeats 800000

/-! ## Part 0. The reflection `wtReflect` on weights -/

/-- `e8Nrm` is invariant under the simple reflection `wtReflect`. -/
lemma e8Nrm_wtReflect (i : Fin 8) (μ : Fin 8 → ℤ) : e8Nrm (wtReflect i μ) = e8Nrm μ := by
  show (Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.e8q
      (Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.e8refl μ i) : ℚ)
    = Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.e8q μ
  rw [Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.e8q_eq_qZ,
    Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ_refl,
    ← Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.e8q_eq_qZ]

/-- The simple reflection on weights is an involution. -/
lemma wtReflect_invol (i : Fin 8) (μ : Fin 8 → ℤ) : wtReflect i (wtReflect i μ) = μ := by
  funext j
  simp only [wtReflect]
  rw [(show ∀ i, CartanMatrix.E₈ i i = 2 from CartanMatrix.E₈_diag)]
  ring

/-! ## Part 1. The matrix of a simple reflection and the invariant-matrix lemma -/

/-- The matrix of the simple reflection `sᵢ` acting on weights in the `ω`-coordinates. -/
def reflMat (i : Fin 8) : Matrix (Fin 8) (Fin 8) ℚ :=
  1 - Matrix.of (fun j a => (CartanMatrix.E₈ i j : ℚ) * (if a = i then 1 else 0))

lemma reflMat_apply' (i j a : Fin 8) :
    reflMat i j a = (if j = a then (1:ℚ) else 0)
      - (CartanMatrix.E₈ i j : ℚ) * (if a = i then (1:ℚ) else 0) := by
  rw [reflMat, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply]

/-- The `i`-th row of `reflMat i` is minus the `i`-th row of the identity. -/
lemma reflMat_row (i a : Fin 8) :
    reflMat i i a = -(1 : Matrix (Fin 8) (Fin 8) ℚ) i a := by
  rw [reflMat_apply', (show ∀ i, CartanMatrix.E₈ i i = 2 from CartanMatrix.E₈_diag), Matrix.one_apply]
  by_cases h : a = i
  · subst h; norm_num
  · rw [if_neg h, if_neg (Ne.symm h)]; norm_num

lemma sum_mul_ite_eq_left (f : Fin 8 → ℚ) (b : Fin 8) :
    (∑ c, f c * (if b = c then (1:ℚ) else 0)) = f b := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc; rw [if_neg (Ne.symm hc), mul_zero]
  · intro hb; exact absurd (Finset.mem_univ b) hb

lemma sum_mul_ite_eq_right (f : Fin 8 → ℚ) (i : Fin 8) :
    (∑ c, f c * (if c = i then (1:ℚ) else 0)) = f i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro c _ hc; rw [if_neg hc, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- The action of `reflMat i` on column vectors is the reflection `wtReflect i`. -/
lemma reflMat_mulVec (i : Fin 8) (μ : Fin 8 → ℤ) :
    reflMat i *ᵥ (fun a => (μ a : ℚ)) = fun a => ((wtReflect i μ) a : ℚ) := by
  funext a
  rw [Matrix.mulVec, dotProduct]
  simp only [reflMat_apply', wtReflect]
  rw [show (∑ x, ((if a = x then (1:ℚ) else 0)
        - (CartanMatrix.E₈ i a : ℚ) * (if x = i then (1:ℚ) else 0)) * (μ x : ℚ))
      = (∑ x, (if a = x then (1:ℚ) else 0) * (μ x : ℚ))
        - (∑ x, ((CartanMatrix.E₈ i a : ℚ) * (if x = i then (1:ℚ) else 0)) * (μ x : ℚ)) from by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring]
  have h1 : (∑ x, (if a = x then (1:ℚ) else 0) * (μ x : ℚ)) = (μ a : ℚ) := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc; rw [if_neg (Ne.symm hc), zero_mul]
    · intro ha; exact absurd (Finset.mem_univ a) ha
  have h2 : (∑ x, ((CartanMatrix.E₈ i a : ℚ) * (if x = i then (1:ℚ) else 0)) * (μ x : ℚ))
      = (CartanMatrix.E₈ i a : ℚ) * (μ i : ℚ) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro c _ hc; rw [if_neg hc, mul_zero, zero_mul]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [h1, h2]
  push_cast
  ring

lemma mul_row_reflMat (T : Matrix (Fin 8) (Fin 8) ℚ) (i c : Fin 8) :
    (reflMat i * T) i c = - T i c := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · rw [reflMat_row]; simp
  · intro d _ hd
    rw [reflMat_row, Matrix.one_apply_ne (Ne.symm hd), neg_zero, zero_mul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- The `(i,b)` entry of `reflMat i * T * (reflMat i)ᵀ`, computed from the fact that the `i`-th
row of `reflMat i` is `-eᵢ`. -/
lemma reflMat_entry (T : Matrix (Fin 8) (Fin 8) ℚ) (i b : Fin 8) :
    (reflMat i * T * (reflMat i)ᵀ) i b
      = - T i b + (CartanMatrix.E₈ i b : ℚ) * T i i := by
  rw [Matrix.mul_apply]
  have h2 : ∀ c, (reflMat i * T) i c * (reflMat i)ᵀ c b
      = - (T i c * (if b = c then (1:ℚ) else 0))
        + (CartanMatrix.E₈ i b : ℚ) * (T i c * (if c = i then (1:ℚ) else 0)) := by
    intro c
    rw [mul_row_reflMat, Matrix.transpose_apply, reflMat_apply']
    ring
  rw [Finset.sum_congr rfl (fun c _ => h2 c), Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [sum_mul_ite_eq_left (fun c => T i c) b, ← Finset.mul_sum,
    sum_mul_ite_eq_right (fun c => T i c) i]

/-- **A symmetric matrix invariant under all the simple reflections is a multiple of the Cartan
matrix.**

The `i`-th simple reflection is the matrix `reflMat i = 1 - (rowᵢ A) ⊗ eᵢᵀ`; its `i`-th row is
`-eᵢᵀ`, so for a symmetric `T` fixed by `Mᵢ T Mᵢᵀ = T` the `(i,b)` entry reads
`-Tᵢ_b + Aᵢ_b Tᵢᵢ = Tᵢ_b`, i.e. `Tᵢ_b = (Tᵢᵢ/2)·Aᵢ_b`.  Hence `T = D·A` with `D` diagonal, and
symmetry of `T` forces `Aᵢ_b (D_bb - D_ii) = 0`; since the Dynkin diagram of `E₈` is connected,
`D` is constant. -/
theorem E8_matrix_eq_smul_of_reflMat_invariant (T : Matrix (Fin 8) (Fin 8) ℚ) (hsymm : Tᵀ = T)
    (hinv : ∀ i, reflMat i * T * (reflMat i)ᵀ = T) :
    T = (T 0 0 / 2) • CartanMatrix.E₈.map (Int.castRingHom ℚ) := by
  have hcol : ∀ i b : Fin 8, T i b = (T i i / 2) * (CartanMatrix.E₈ i b : ℚ) := by
    intro i b
    have h := reflMat_entry T i b
    have h2 : (reflMat i * T * (reflMat i)ᵀ) i b = T i b := by rw [hinv i]
    rw [h2] at h
    linarith
  -- `D` is the diagonal of `T` halved
  set D : Fin 8 → ℚ := fun i => T i i / 2 with hD
  have hTA : ∀ i b : Fin 8, T i b = D i * (CartanMatrix.E₈ i b : ℚ) := fun i b => hcol i b
  -- symmetry: `Aᵢ_b (D_bb - D_ii) = 0`
  have hsym : ∀ i b : Fin 8, (D b - D i) * (CartanMatrix.E₈ i b : ℚ) = 0 := by
    intro i b
    have h1 : T b i = T i b := by
      have h := congrFun (congrFun hsymm i) b
      simpa [Matrix.transpose_apply] using h
    rw [hTA b i, hTA i b] at h1
    have hs : (CartanMatrix.E₈ b i : ℚ) = (CartanMatrix.E₈ i b : ℚ) := by
      exact_mod_cast (Commons.LinearAlgebra.Matrix.Cartan.E8_diag_offdiag_symm.1 b i)
    rw [hs] at h1
    nlinarith [h1]
  have key : ∀ i b : Fin 8, CartanMatrix.E₈ i b ≠ 0 → D i = D b := by
    intro i b h
    have h' := hsym i b
    have hA : (CartanMatrix.E₈ i b : ℚ) ≠ 0 := by exact_mod_cast h
    have h0 : D b - D i = 0 := by
      rcases mul_eq_zero.mp h' with h1 | h1
      · exact h1
      · exact absurd h1 hA
    linarith
  have hD0 : ∀ i : Fin 8, D i = D 0 := by
    have h20 : D 2 = D 0 := key 2 0 (by decide)
    have h32 : D 3 = D 2 := key 3 2 (by decide)
    have h13 : D 1 = D 3 := key 1 3 (by decide)
    have h43 : D 4 = D 3 := key 4 3 (by decide)
    have h54 : D 5 = D 4 := key 5 4 (by decide)
    have h65 : D 6 = D 5 := key 6 5 (by decide)
    have h76 : D 7 = D 6 := key 7 6 (by decide)
    intro i
    fin_cases i
    · rfl
    · exact h13.trans (h32.trans h20)
    · exact h20
    · exact h32.trans h20
    · exact h43.trans (h32.trans h20)
    · exact h54.trans (h43.trans (h32.trans h20))
    · exact h65.trans (h54.trans (h43.trans (h32.trans h20)))
    · exact h76.trans (h65.trans (h54.trans (h43.trans (h32.trans h20))))
  ext a b
  rw [hTA a b, hD0 a]
  simp [hD, Matrix.smul_apply, smul_eq_mul]




/-! ## Part 2. The root-sum matrix `∑_{μ ∈ rt} μ μᵀ` -/

/-- The matrix `∑_{μ ∈ rt} μ μᵀ` attached to a set `rt` of weights in the `ω`-coordinates. -/
def rootSumMat (rt : Finset (Fin 8 → ℤ)) : Matrix (Fin 8) (Fin 8) ℚ :=
  fun a b => ∑ μ ∈ rt, (μ a : ℚ) * (μ b : ℚ)

lemma rootSumMat_symm (rt : Finset (Fin 8 → ℤ)) : (rootSumMat rt)ᵀ = rootSumMat rt := by
  ext a b
  simp only [Matrix.transpose_apply, rootSumMat]
  exact Finset.sum_congr rfl fun μ _ => by ring

/-- The set of roots is permuted by every simple reflection. -/
lemma roots_image_wtReflect {rt : Finset (Fin 8 → ℤ)}
    (hrt : ∀ μ, μ ∈ rt ↔ μ ≠ 0 ∧ e8Nrm μ = 2) (i : Fin 8) :
    rt.image (wtReflect i) = rt := by
  have hzero : ∀ ν : Fin 8 → ℤ, wtReflect i ν = 0 ↔ ν = 0 := by
    intro ν
    constructor
    · intro h
      have h' := congrArg (wtReflect i) h
      rw [wtReflect_invol] at h'
      have h0 : wtReflect i (0 : Fin 8 → ℤ) = 0 := by funext j; simp [wtReflect]
      rwa [h0] at h'
    · intro h; rw [h]; funext j; simp [wtReflect]
  have hmem : ∀ ν : Fin 8 → ℤ, wtReflect i ν ∈ rt ↔ ν ∈ rt := by
    intro ν
    rw [hrt, hrt]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h0 => h1 ((hzero ν).mpr h0), by rw [← e8Nrm_wtReflect i ν]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h0 => h1 ((hzero ν).mp h0), by rw [e8Nrm_wtReflect i ν]; exact h2⟩
  refine Finset.ext fun μ => ?_
  rw [Finset.mem_image]
  constructor
  · rintro ⟨ν, hν, rfl⟩
    exact (hmem ν).mpr hν
  · intro hμ
    refine ⟨wtReflect i μ, ?_, wtReflect_invol i μ⟩
    rw [hmem]
    exact hμ

lemma roots_injective_wtReflect {rt : Finset (Fin 8 → ℤ)} (i : Fin 8) :
    ∀ x ∈ rt, ∀ y ∈ rt, wtReflect i x = wtReflect i y → x = y := by
  intro x _ y _ h
  have h' := congrArg (wtReflect i) h
  rwa [wtReflect_invol, wtReflect_invol] at h'

/-- **The column condition for the root-sum matrix.**  Since the roots are permuted by the
reflection `sᵢ`, and `sᵢ` fixes the `i`-th coordinate of a weight up to sign and subtracts
`μᵢ Aᵢ_b` from the `b`-th, the `(i,b)` entry `∑_μ μᵢ μ_b` satisfies
`∑_μ μᵢ μ_b = -∑_μ μᵢ μ_b + Aᵢ_b ∑_μ μᵢ²`, i.e. `Tᵢ_b = (Tᵢᵢ/2) Aᵢ_b`. -/
lemma rootSumMat_self {rt : Finset (Fin 8 → ℤ)}
    (hrt : ∀ μ, μ ∈ rt ↔ μ ≠ 0 ∧ e8Nrm μ = 2) (i b : Fin 8) :
    rootSumMat rt i b = (rootSumMat rt i i / 2) * (CartanMatrix.E₈ i b : ℚ) := by
  have hpt : ∀ μ : Fin 8 → ℤ,
      ((wtReflect i μ) i : ℚ) * ((wtReflect i μ) b : ℚ)
        = - ((μ i : ℚ) * (μ b : ℚ))
          + (CartanMatrix.E₈ i b : ℚ) * ((μ i : ℚ) * (μ i : ℚ)) := by
    intro μ
    simp only [wtReflect, (show ∀ i, CartanMatrix.E₈ i i = 2 from CartanMatrix.E₈_diag)]
    push_cast
    ring
  have hperm : (∑ μ ∈ rt, ((wtReflect i μ) i : ℚ) * ((wtReflect i μ) b : ℚ))
      = ∑ μ ∈ rt, (μ i : ℚ) * (μ b : ℚ) := by
    conv_rhs => rw [← roots_image_wtReflect hrt i]
    rw [Finset.sum_image (roots_injective_wtReflect i)]
  have hL : (∑ μ ∈ rt, ((wtReflect i μ) i : ℚ) * ((wtReflect i μ) b : ℚ))
      = - (∑ μ ∈ rt, (μ i : ℚ) * (μ b : ℚ))
        + (CartanMatrix.E₈ i b : ℚ) * (∑ μ ∈ rt, (μ i : ℚ) * (μ i : ℚ)) := by
    rw [Finset.sum_congr rfl fun μ _ => hpt μ]
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum]
  have hEq : rootSumMat rt i b
      = - rootSumMat rt i b + (CartanMatrix.E₈ i b : ℚ) * rootSumMat rt i i := by
    show (∑ μ ∈ rt, (μ i : ℚ) * (μ b : ℚ))
      = - (∑ μ ∈ rt, (μ i : ℚ) * (μ b : ℚ))
        + (CartanMatrix.E₈ i b : ℚ) * (∑ μ ∈ rt, (μ i : ℚ) * (μ i : ℚ))
    conv_lhs => rw [← hperm]
    exact hL
  linarith

/-! ## Part 3. A symmetric matrix satisfying the column condition is a multiple of `A` -/

/-- **A symmetric `8 × 8` matrix `T` with `Tᵢ_b = (Tᵢᵢ/2) Aᵢ_b` is a scalar multiple of the `E₈`
Cartan matrix.**

Write `D` for the diagonal matrix with `Dᵢᵢ = Tᵢᵢ/2`; the hypothesis says `T = D A`.  Symmetry of
`T` gives `Aᵢ_b (D_bb - Dᵢᵢ) = 0`, and since the Dynkin diagram of `E₈` is connected (`Aᵢ_b ≠ 0`
along the chain `0-2-3-1`, `3-4-5-6-7`), `D` is constant. -/
theorem E8_matrix_eq_smul_of_col (T : Matrix (Fin 8) (Fin 8) ℚ) (hsymm : Tᵀ = T)
    (hcol : ∀ i b : Fin 8, T i b = (T i i / 2) * (CartanMatrix.E₈ i b : ℚ)) :
    T = (T 0 0 / 2) • CartanMatrix.E₈.map (Int.castRingHom ℚ) := by
  set D : Fin 8 → ℚ := fun i => T i i / 2 with hD
  have hTA : ∀ i b : Fin 8, T i b = D i * (CartanMatrix.E₈ i b : ℚ) := fun i b => hcol i b
  have hsym : ∀ i b : Fin 8, (D b - D i) * (CartanMatrix.E₈ i b : ℚ) = 0 := by
    intro i b
    have h1 : T b i = T i b := by
      have h := congrFun (congrFun hsymm i) b
      simpa [Matrix.transpose_apply] using h
    rw [hTA b i, hTA i b] at h1
    have hs : (CartanMatrix.E₈ b i : ℚ) = (CartanMatrix.E₈ i b : ℚ) := by
      exact_mod_cast (Commons.LinearAlgebra.Matrix.Cartan.E8_diag_offdiag_symm.1 b i)
    rw [hs] at h1
    nlinarith [h1]
  have key : ∀ i b : Fin 8, CartanMatrix.E₈ i b ≠ 0 → D i = D b := by
    intro i b h
    have h' := hsym i b
    have hA : (CartanMatrix.E₈ i b : ℚ) ≠ 0 := by exact_mod_cast h
    have h0 : D b - D i = 0 := by
      rcases mul_eq_zero.mp h' with h1 | h1
      · exact h1
      · exact absurd h1 hA
    linarith
  have hD0 : ∀ i : Fin 8, D i = D 0 := by
    have h20 : D 2 = D 0 := key 2 0 (by decide)
    have h32 : D 3 = D 2 := key 3 2 (by decide)
    have h13 : D 1 = D 3 := key 1 3 (by decide)
    have h43 : D 4 = D 3 := key 4 3 (by decide)
    have h54 : D 5 = D 4 := key 5 4 (by decide)
    have h65 : D 6 = D 5 := key 6 5 (by decide)
    have h76 : D 7 = D 6 := key 7 6 (by decide)
    intro i
    fin_cases i
    · rfl
    · exact h13.trans (h32.trans h20)
    · exact h20
    · exact h32.trans h20
    · exact h43.trans (h32.trans h20)
    · exact h54.trans (h43.trans (h32.trans h20))
    · exact h65.trans (h54.trans (h43.trans (h32.trans h20)))
    · exact h76.trans (h65.trans (h54.trans (h43.trans (h32.trans h20))))
  ext a b
  rw [hTA a b, hD0 a]
  simp [hD, Matrix.smul_apply, smul_eq_mul]

/-! ## Part 4. Sums of three families of indices -/

/-- Reorder a triple sum: the `(a,b)`-sums are exchanged with the `c`-sum. -/
lemma sum_comm3 {R α β γ : Type*} [AddCommMonoid R] (s : Finset α) (t : Finset β)
    (u : Finset γ) (f : α → β → γ → R) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c) = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, f a b c := by
  have h1 : (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c) = ∑ a ∈ s, ∑ c ∈ u, ∑ b ∈ t, f a b c :=
    Finset.sum_congr rfl fun a _ => Finset.sum_comm
  rw [h1, Finset.sum_comm]

/-- A sum over a `Finset` as a sum over the corresponding subtype. -/
lemma sum_finset_eq_sum_subtype {M : Type*} [AddCommMonoid M] (T : Finset (Fin 8 → ℤ))
    (g : (Fin 8 → ℤ) → M) :
    (∑ μ : ↥T, g (μ : Fin 8 → ℤ)) = ∑ μ ∈ T, g μ := by
  rw [← Finset.attach_eq_univ (s := T), Finset.sum_attach]

/-! ## Part 5. Traces of `ad Hᵢ ∘ ad Hⱼ` on the weight spaces -/

/-- `ad (H i)` acts on the weight space `e8W μ` by the scalar `μ i`. -/
lemma e8W_ad (i : Fin 8) {μ : Fin 8 → ℤ} {x : L8} (hx : x ∈ e8W μ) :
    ⁅SerreH i, x⁆ = (μ i : ℂ) • x :=
  (mem_W_iff (μ := fun j => ((μ j : ℤ) : ℂ))).mp hx i

/-- `(ad H i) ∘ (ad H j)` acts on `e8W μ` by the scalar `μ i * μ j`. -/
lemma e8W_ad_comp (i j : Fin 8) {μ : Fin 8 → ℤ} {x : L8} (hx : x ∈ e8W μ) :
    (LieAlgebra.ad ℂ L8 (SerreH i) ∘ₗ LieAlgebra.ad ℂ L8 (SerreH j)) x
      = ((μ i : ℂ) * (μ j : ℂ)) • x := by
  rw [LinearMap.comp_apply, LieAlgebra.ad_apply, LieAlgebra.ad_apply, e8W_ad j hx, lie_smul,
    e8W_ad i hx, smul_smul, mul_comm (μ j : ℂ) (μ i : ℂ)]

/-- The trace of `(ad H i) ∘ (ad H j)` on the weight space `e8W μ` is `μᵢ μⱼ dim e8W μ`. -/
lemma trace_restrict_e8W (i j : Fin 8) (μ : Fin 8 → ℤ)
    (hf : Set.MapsTo (LieAlgebra.ad ℂ L8 (SerreH i) ∘ₗ LieAlgebra.ad ℂ L8 (SerreH j))
      (e8W μ) (e8W μ)) :
    LinearMap.trace ℂ ↥(e8W μ)
        ((LieAlgebra.ad ℂ L8 (SerreH i) ∘ₗ LieAlgebra.ad ℂ L8 (SerreH j)).restrict hf)
      = ((μ i : ℂ) * (μ j : ℂ)) * (Module.finrank ℂ ↥(e8W μ) : ℂ) := by
  have h1 : (LieAlgebra.ad ℂ L8 (SerreH i) ∘ₗ LieAlgebra.ad ℂ L8 (SerreH j)).restrict hf
      = ((μ i : ℂ) * (μ j : ℂ)) • (1 : Module.End ℂ ↥(e8W μ)) := by
    ext x
    rw [LinearMap.smul_apply, Module.End.one_apply]
    exact e8W_ad_comp i j x.2
  rw [h1, LinearMap.map_smul, LinearMap.trace_one, smul_eq_mul]

/-! ## Part 6. The inverse of the `E₈` Cartan matrix over `ℚ` -/

/-- `A⁻¹ A = 1` for the `E₈` Cartan matrix over `ℚ`. -/
lemma Aq_inv_mul :
    (CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹ * CartanMatrix.E₈.map (Int.castRingHom ℚ)
      = 1 := by
  rw [Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8q_inv]
  rw [show CartanMatrix.E₈.map (Int.castRingHom ℚ)
      = Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8q from rfl]
  rw [← Matrix.map_mul, Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv_mul_E8]
  ext i j
  simp [Matrix.map_apply, Matrix.one_apply]

/-! ## Part 7. The Killing form on the Cartan subalgebra -/

/-- **The Killing form on the Cartan subalgebra of the Serre-constructed `e₈`.**
For the Serre `H`-generators, `κ (SerreH i) (SerreH j) = 60 · Aᵢⱼ` where `A = CartanMatrix.E₈`.

Proof route: `killingForm ℂ L x y = tr (ad x ∘ ad y)`; on the Cartan subalgebra the operators
`ad (SerreH i)` are simultaneously diagonalizable with the integral weight decomposition
`e₈ = ⊕_μ e8W μ` (`Commons.Algebra.Lie.e8W_iSup_eq_top`, `e8W_iSupIndep`), the zero weight space
has dimension `8` (`Commons.Algebra.Lie.SerreConstruction.e8_zero_weightSpace_finrank`) and
contributes `0` to the trace, and every nonzero weight `μ` satisfies `e8W μ ≠ ⊥ → μᵀA⁻¹μ = 2`
(`Commons.Algebra.Lie.SerreConstruction.weight_norm_two`), the root spaces being one-dimensional
(`e8_root_weightSpace_finrank_eq_one`).  Hence
`κ (SerreH i) (SerreH j) = ∑_{μ ∈ Φ} μᵢ μⱼ`, over the 240-element root set of
`Commons.Algebra.Lie.SerreConstruction.exists_finset_e8_roots` (or `e8_rootVector_card`); the sum
evaluates to `60 · Aᵢⱼ` by a finite check over the root list. -/
theorem killingForm_SerreH (i j : Fin 8) :
    killingForm ℂ (LieAlgebra.e₈ ℂ)
      (Commons.Algebra.Lie.SerreConstruction.SerreH i)
      (Commons.Algebra.Lie.SerreConstruction.SerreH j)
    = 60 * ((CartanMatrix.E₈ i j : ℤ) : ℂ) := by
  classical
  obtain ⟨rt, hrt_mem, hrt_card⟩ := exists_finset_e8_roots
  -- ------------------------------------------------------------------
  -- Step 1: rewrite the Killing form as the trace of `ad Hᵢ ∘ ad Hⱼ`
  -- ------------------------------------------------------------------
  have hk : killingForm ℂ (LieAlgebra.e₈ ℂ) (SerreH i) (SerreH j)
      = LinearMap.trace ℂ L8
          (LieAlgebra.ad ℂ L8 (SerreH i) ∘ₗ LieAlgebra.ad ℂ L8 (SerreH j)) := by
    rw [LieModule.traceForm_apply_apply]
    rfl
  -- ------------------------------------------------------------------
  -- Step 2: the weight decomposition and its internal direct sum structure
  -- ------------------------------------------------------------------
  set T : Finset (Fin 8 → ℤ) := insert 0 rt with hT
  have h0rt : (0 : Fin 8 → ℤ) ∉ rt := fun h => ((hrt_mem 0).mp h).1 rfl
  have hsupp : ∀ μ : Fin 8 → ℤ, μ ∉ T → e8W μ = ⊥ := by
    intro μ hμ
    have hne : μ ≠ 0 := by
      rintro rfl
      exact hμ (by rw [hT]; exact Finset.mem_insert_self _ _)
    have hnr : e8Nrm μ ≠ 2 := fun h2 =>
      hμ (by rw [hT]; exact Finset.mem_insert_of_mem ((hrt_mem μ).mpr ⟨hne, h2⟩))
    exact e8W_eq_bot_of_not_root μ hne hnr
  have hind : iSupIndep (fun μ : ↥T => e8W (μ : Fin 8 → ℤ)) := by
    refine Commons.LinearAlgebra.Eigenspace.iSupIndep_eigenspace_of_commute_of_torsionfree
      (R := ℂ) (M := L8) (ι := Fin 8) (κ := ↥T)
      (T := fun i => LieAlgebra.ad ℂ L8 (SerreH i))
      (χ := fun μ i => (((μ : ↥T) : Fin 8 → ℤ) i : ℂ)) ?_ ?_
    · intro a b; exact ad_SerreH_commute a b
    · intro μ ν h
      by_contra hcon
      push Not at hcon
      exact h (Subtype.ext (funext fun i => by exact_mod_cast hcon i))
  have hspan : (⨆ μ : ↥T, e8W (μ : Fin 8 → ℤ)) = ⊤ := by
    rw [eq_top_iff, ← e8W_iSup_eq_top]
    refine iSup_le (fun μ => ?_)
    by_cases h : μ ∈ T
    · exact le_iSup (fun ν : ↥T => e8W (ν : Fin 8 → ℤ)) ⟨μ, h⟩
    · rw [hsupp μ h]; exact bot_le
  have hinternal := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hspan
  have hmapsTo : ∀ μ : ↥T, Set.MapsTo
      (LieAlgebra.ad ℂ L8 (SerreH i) ∘ₗ LieAlgebra.ad ℂ L8 (SerreH j))
      (e8W (μ : Fin 8 → ℤ)) (e8W (μ : Fin 8 → ℤ)) := fun μ x hx => by
    rw [e8W_ad_comp i j hx]
    exact Submodule.smul_mem _ _ hx
  -- ------------------------------------------------------------------
  -- Step 3: compute the trace by summing over the root spaces
  -- ------------------------------------------------------------------
  have htrace : killingForm ℂ (LieAlgebra.e₈ ℂ) (SerreH i) (SerreH j)
      = ((rootSumMat rt i j : ℚ) : ℂ) := by
    rw [hk, LinearMap.trace_eq_sum_trace_restrict (R := ℂ) hinternal hmapsTo]
    rw [Finset.sum_congr rfl
      (fun (μ : ↥T) _ => trace_restrict_e8W i j (μ : Fin 8 → ℤ) (hmapsTo μ))]
    rw [sum_finset_eq_sum_subtype T (fun μ : Fin 8 → ℤ =>
      ((μ i : ℂ) * (μ j : ℂ)) * (Module.finrank ℂ ↥(e8W μ) : ℂ))]
    rw [hT, Finset.sum_insert h0rt]
    simp only [Pi.zero_apply, Int.cast_zero, mul_zero, zero_mul, zero_add]
    rw [show (∑ μ ∈ rt, ((μ i : ℂ) * (μ j : ℂ)) * (Module.finrank ℂ ↥(e8W μ) : ℂ))
        = ∑ μ ∈ rt, (μ i : ℂ) * (μ j : ℂ) from by
      refine Finset.sum_congr rfl fun μ hμ => ?_
      have hfin : Module.finrank ℂ ↥(e8W μ) = 1 := by
        obtain ⟨hne, h2⟩ := (hrt_mem μ).mp hμ
        exact e8_root_weightSpace_finrank_eq_one μ hne h2
      rw [hfin]
      norm_num]
    show (∑ μ ∈ rt, (μ i : ℂ) * (μ j : ℂ)) = ((rootSumMat rt i j : ℚ) : ℂ)
    rw [show rootSumMat rt i j = ∑ μ ∈ rt, (μ i : ℚ) * (μ j : ℚ) from rfl]
    push_cast
    rfl
  -- ------------------------------------------------------------------
  -- Step 4: the matrix of roots is a multiple of the Cartan matrix
  -- ------------------------------------------------------------------
  have hS : rootSumMat rt = (rootSumMat rt 0 0 / 2) • CartanMatrix.E₈.map (Int.castRingHom ℚ) :=
    E8_matrix_eq_smul_of_col (rootSumMat rt) (rootSumMat_symm rt)
      (fun a b => rootSumMat_self hrt_mem a b)
  -- ------------------------------------------------------------------
  -- Step 5: determine the constant by contracting with `A⁻¹`
  -- ------------------------------------------------------------------
  have hcontr1 : ∑ a, ∑ b, (CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹ a b * rootSumMat rt a b
      = 480 := by
    have h1 : ∑ a, ∑ b, (CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹ a b * rootSumMat rt a b
        = ∑ a, ∑ b, ∑ μ ∈ rt, (CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹ a b
            * ((μ a : ℚ) * (μ b : ℚ)) := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [show rootSumMat rt a b = ∑ μ ∈ rt, (μ a : ℚ) * (μ b : ℚ) from rfl, Finset.mul_sum]
    rw [h1, sum_comm3 Finset.univ Finset.univ rt]
    rw [Finset.sum_congr rfl (fun μ _ => by
      show (∑ a, ∑ b, (CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹ a b
        * ((μ a : ℚ) * (μ b : ℚ))) = e8Nrm μ
      rw [e8Nrm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)]
    rw [show (∑ μ ∈ rt, e8Nrm μ) = ∑ μ ∈ rt, (2 : ℚ) from
      Finset.sum_congr rfl (fun μ hμ => by
        show e8Nrm μ = (2 : ℚ)
        exact ((hrt_mem μ).mp hμ).2)]
    rw [Finset.sum_const, hrt_card]
    norm_num
  have hcontr2 : ∑ a, ∑ b, (CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹ a b * rootSumMat rt a b
      = 8 * (rootSumMat rt 0 0 / 2) := by
    conv_lhs => rw [hS]
    simp only [Matrix.smul_apply, smul_eq_mul]
    have step : ∀ a, ∑ b, (CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹ a b
        * ((rootSumMat rt 0 0 / 2) * (CartanMatrix.E₈.map (Int.castRingHom ℚ)) a b)
        = rootSumMat rt 0 0 / 2 := by
      intro a
      calc ∑ b, (CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹ a b
            * ((rootSumMat rt 0 0 / 2) * (CartanMatrix.E₈.map (Int.castRingHom ℚ)) a b)
          = (rootSumMat rt 0 0 / 2) * ∑ b, (CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹ a b
              * (CartanMatrix.E₈.map (Int.castRingHom ℚ)) b a := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [show (CartanMatrix.E₈.map (Int.castRingHom ℚ)) a b
                = (CartanMatrix.E₈.map (Int.castRingHom ℚ)) b a from by
              simp only [Matrix.map_apply, Int.coe_castRingHom]
              exact_mod_cast (Commons.LinearAlgebra.Matrix.Cartan.E8_diag_offdiag_symm.1 a b)]
            ring
        _ = (rootSumMat rt 0 0 / 2)
              * ((CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹
                  * CartanMatrix.E₈.map (Int.castRingHom ℚ)) a a := by
            rw [Matrix.mul_apply]
        _ = (rootSumMat rt 0 0 / 2) * 1 := by rw [Aq_inv_mul, Matrix.one_apply_eq]
        _ = rootSumMat rt 0 0 / 2 := by ring
    rw [Finset.sum_congr rfl (fun a _ => step a), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hc : rootSumMat rt 0 0 / 2 = (60 : ℚ) := by linarith
  -- ------------------------------------------------------------------
  -- Step 6: conclusion
  -- ------------------------------------------------------------------
  have h60 : ∀ a b : Fin 8, rootSumMat rt a b = 60 * (CartanMatrix.E₈ a b : ℚ) := by
    intro a b
    have h := congrFun (congrFun hS a) b
    rw [Matrix.smul_apply, smul_eq_mul] at h
    rw [h, hc]
    simp [Matrix.map_apply, Int.coe_castRingHom]
  rw [htrace]
  have hfin : ((rootSumMat rt i j : ℚ) : ℂ) = 60 * ((CartanMatrix.E₈ i j : ℤ) : ℂ) := by
    rw [h60 i j]
    push_cast
    ring
  exact hfin

end

end Commons.Algebra.Lie.SerreConstruction
