import Mathlib
import Submission.Work.HP.Sig2.GamTwoDefs
import Submission.Work.HP.Vero.SigmaLinalg
import Submission.Work.HP.Sig2.RW.three_solve
import Submission.Work.HP.Sig2.RW.gramDet_ne_zero

/-!
# The row witness `rᵢ(a)` against the orthogonal complement of `{x,y}`

This file proves `Work.HP.Sig2.RowWitness`: if a real coefficient vector `a : Mon 2 n → ℝ` of a
quadratic form in `n+1` variables does not lie in `V₃ = span_ℝ{ν₂(x), ν₂(y), ν₂(x+y)}`, then some
row `rᵢ(a)` (`(rᵢ a) j = a (XᵢXⱼ)`) pairs nontrivially with an integer vector orthogonal to both
`x` and `y`.

The proof route is the one of Browning–Le Boudec–Sawin, (Equality sigma), but with `σ` replaced by
the symmetric matrix `matA n a` with entries `(matA a) i j = a (XᵢXⱼ)`: the pairing of the row
`rᵢ(a)` with `v` is the `i`-th entry of `(matA a) *ᵥ v`, so the vanishing hypothesis says that
`matA n a` kills the real span `W` of `{v : ℤ^{n+1} | ⟨v,x⟩ = ⟨v,y⟩ = 0}` — a submodule which,
by `Work.HP.Vero.span_realify_latOrth_inf`, is the orthogonal complement of `span_ℝ{toR x, toR y}`.

The core linear-algebra statement (`core`, proved here) is then that a symmetric matrix killing the
orthogonal complement of `span{x,y}` for linearly independent `x,y` is a linear combination of the
three rank-one matrices `xxᵀ, yyᵀ, (x+y)(x+y)ᵀ`.  Under the linear bijection `a ↦ matA a` those
three matrices are the images of `ν₂(x), ν₂(y), ν₂(x+y)`, so `a ∈ V₃`, contradiction.
-/

set_option autoImplicit false
noncomputable section

open Work.HP Finset
open scoped Matrix

namespace Work.HP.Sig2

/-! ## `pairMon` is surjective and `matA` is injective -/

/-- Every degree-two monomial `X^m` is of the form `XᵢXⱼ`. -/
theorem pairMon_surj {n : ℕ} (m : Mon 2 n) : ∃ i j : Fin (n + 1), Vero.pairMon n i j = m := by
  classical
  have hsum : (∑ i : Fin (n + 1), (m.1 i).val) = 2 := m.2
  have hle : ∀ i : Fin (n + 1), (m.1 i).val ≤ 2 := by
    intro i
    have h := Finset.single_le_sum (f := fun i : Fin (n + 1) => (m.1 i).val)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin (n + 1), (m.1 i0).val ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h0 : (∑ i : Fin (n + 1), (m.1 i).val) = 0 := Finset.sum_eq_zero (fun i _ => hc i)
    omega
  rcases Nat.lt_or_ge (m.1 i0).val 2 with hlt | hge
  · -- `(m.1 i0).val = 1`: there is a second index carrying the remaining `1`
    have hi0_eq : (m.1 i0).val = 1 := by omega
    have hrest : (∑ i ∈ Finset.univ.erase i0, (m.1 i).val) = 1 := by
      have h := Finset.sum_erase_add (Finset.univ : Finset (Fin (n + 1)))
        (fun i : Fin (n + 1) => (m.1 i).val) (Finset.mem_univ i0)
      omega
    obtain ⟨j, hjmem, hjne⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (show (∑ i ∈ Finset.univ.erase i0, (m.1 i).val) ≠ 0 by omega)
    have hji : j ≠ i0 := (Finset.mem_erase.mp hjmem).1
    have hj1 : (m.1 j).val = 1 := by
      have h := Finset.single_le_sum (f := fun i : Fin (n + 1) => (m.1 i).val)
        (fun i _ => Nat.zero_le _) hjmem
      omega
    have hzero : ∀ r : Fin (n + 1), r ≠ i0 → r ≠ j → (m.1 r).val = 0 := by
      intro r hr1 hr2
      have hsum0 : (∑ i ∈ (Finset.univ.erase i0).erase j, (m.1 i).val) = 0 := by
        have h := Finset.sum_erase_add ((Finset.univ : Finset (Fin (n + 1))).erase i0)
          (fun i : Fin (n + 1) => (m.1 i).val) hjmem
        omega
      have hmem : r ∈ (Finset.univ.erase i0).erase j :=
        Finset.mem_erase.mpr ⟨hr2, Finset.mem_erase.mpr ⟨hr1, Finset.mem_univ r⟩⟩
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le _)).mp hsum0 r hmem
    refine ⟨i0, j, ?_⟩
    apply Subtype.ext
    funext r
    apply Fin.ext
    rw [pairMon_val_eq]
    by_cases hr1 : r = i0
    · subst hr1
      rw [if_pos rfl, if_neg (fun h : r = j => hji h.symm), add_zero]
      exact hi0_eq.symm
    · by_cases hr2 : r = j
      · subst hr2
        rw [if_neg hji, if_pos rfl, zero_add]
        exact hj1.symm
      · rw [if_neg hr1, if_neg hr2, add_zero]
        exact (hzero r hr1 hr2).symm
  · -- `(m.1 i0).val = 2`: everything is concentrated at `i0`
    have hi0_eq : (m.1 i0).val = 2 := by omega
    refine ⟨i0, i0, ?_⟩
    apply Subtype.ext
    funext r
    apply Fin.ext
    rw [pairMon_val_eq]
    by_cases hr : r = i0
    · subst hr
      rw [if_pos rfl]
      omega
    · have hsum0 : (∑ i ∈ Finset.univ.erase i0, (m.1 i).val) = 0 := by
        have h := Finset.sum_erase_add (Finset.univ : Finset (Fin (n + 1)))
          (fun i : Fin (n + 1) => (m.1 i).val) (Finset.mem_univ i0)
        omega
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le _)).mp hsum0 r
        (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩)
      rw [if_neg hr, add_zero]
      exact hz.symm

/-- The matrix `matA n a` determines the coefficient vector `a`. -/
theorem matA_injective {n : ℕ} : Function.Injective (Vero.matA n) := by
  intro a b hab
  funext m
  obtain ⟨i, j, hij⟩ := pairMon_surj m
  have h := congrFun (congrFun hab i) j
  rw [Vero.matA_apply, Vero.matA_apply] at h
  rw [← hij]
  exact h

/-- `matA` of the Veronese vector `ν₂(x)` is the rank-one matrix `xᵢxⱼ`. -/
theorem matA_veronese {n : ℕ} (x : Fin (n + 1) → ℤ) (i j : Fin (n + 1)) :
    Vero.matA n (toR (veronese 2 n x)) i j = (x i : ℝ) * (x j : ℝ) := by
  show ((veronese 2 n x) (Vero.pairMon n i j) : ℝ) = (x i : ℝ) * (x j : ℝ)
  rw [Vero.veronese_pairMon]
  push_cast
  ring

/-! ## The orthogonal decomposition of `ℝ^{n+1}` along `span{x,y}` -/

section dotRAux

variable {ι : Type*} [Fintype ι]

lemma rw_dotR_comm (v w : ι → ℝ) : dotR v w = dotR w v := by
  simp only [dotR]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma rw_dotR_add (v w₁ w₂ : ι → ℝ) : dotR v (w₁ + w₂) = dotR v w₁ + dotR v w₂ := by
  simp only [dotR, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma rw_dotR_sub (v w₁ w₂ : ι → ℝ) : dotR v (w₁ - w₂) = dotR v w₁ - dotR v w₂ := by
  simp only [dotR, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma rw_dotR_smul (v w : ι → ℝ) (t : ℝ) : dotR v (t • w) = t * dotR v w := by
  simp only [dotR, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

end dotRAux

/-- Solving the `2 × 2` Gram system: if `a * c - b ^ 2 ≠ 0`, then
`λ = (c p - b q)/(ac - b²)`, `μ = (a q - b p)/(ac - b²)` solves `λ a + μ b = p`. -/
lemma rw_gram_solve_x (a b c p q : ℝ) (h : a * c - b ^ 2 ≠ 0) :
    ((c * p - b * q) / (a * c - b ^ 2)) * a + ((a * q - b * p) / (a * c - b ^ 2)) * b = p := by
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff h]
  ring

/-- The second equation of the same `2 × 2` Gram system: `λ b + μ c = q`. -/
lemma rw_gram_solve_y (a b c p q : ℝ) (h : a * c - b ^ 2 ≠ 0) :
    ((c * p - b * q) / (a * c - b ^ 2)) * b + ((a * q - b * p) / (a * c - b ^ 2)) * c = q := by
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff h]
  ring

/-- Any vector of `ℝ^{n+1}` splits as a vector of `span_ℝ {x,y}` plus a vector orthogonal to both
`x` and `y`, as soon as the Gram determinant `‖x‖²‖y‖² - ⟨x,y⟩²` does not vanish.  Explicitly,
`s = λ • x + μ • y` and `w = z - s` with `λ = (⟨y,y⟩⟨x,z⟩ - ⟨x,y⟩⟨y,z⟩)/Δ` and
`μ = (⟨x,x⟩⟨y,z⟩ - ⟨x,y⟩⟨x,z⟩)/Δ`. -/
lemma rw_exists_span_add_orth {n : ℕ} (x y z : Fin (n + 1) → ℝ)
    (hΔ : dotR x x * dotR y y - dotR x y ^ 2 ≠ 0) :
    ∃ s w : Fin (n + 1) → ℝ, s ∈ Submodule.span ℝ ({x, y} : Set (Fin (n + 1) → ℝ)) ∧
      dotR x w = 0 ∧ dotR y w = 0 ∧ z = s + w := by
  refine ⟨((dotR y y * dotR x z - dotR x y * dotR y z) / (dotR x x * dotR y y - dotR x y ^ 2)) • x
      + ((dotR x x * dotR y z - dotR x y * dotR x z) / (dotR x x * dotR y y - dotR x y ^ 2)) • y,
    z - (((dotR y y * dotR x z - dotR x y * dotR y z)
        / (dotR x x * dotR y y - dotR x y ^ 2)) • x
      + ((dotR x x * dotR y z - dotR x y * dotR x z)
        / (dotR x x * dotR y y - dotR x y ^ 2)) • y), ?_, ?_, ?_, ?_⟩
  · exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · have h1 : dotR x (z - (((dotR y y * dotR x z - dotR x y * dotR y z)
          / (dotR x x * dotR y y - dotR x y ^ 2)) • x
        + ((dotR x x * dotR y z - dotR x y * dotR x z)
          / (dotR x x * dotR y y - dotR x y ^ 2)) • y))
        = dotR x z - (((dotR y y * dotR x z - dotR x y * dotR y z)
            / (dotR x x * dotR y y - dotR x y ^ 2)) * dotR x x
          + ((dotR x x * dotR y z - dotR x y * dotR x z)
            / (dotR x x * dotR y y - dotR x y ^ 2)) * dotR x y) := by
      rw [rw_dotR_sub, rw_dotR_add, rw_dotR_smul, rw_dotR_smul]
    rw [h1]
    have hkey := rw_gram_solve_x (dotR x x) (dotR x y) (dotR y y) (dotR x z) (dotR y z) hΔ
    linarith
  · have h1 : dotR y (z - (((dotR y y * dotR x z - dotR x y * dotR y z)
          / (dotR x x * dotR y y - dotR x y ^ 2)) • x
        + ((dotR x x * dotR y z - dotR x y * dotR x z)
          / (dotR x x * dotR y y - dotR x y ^ 2)) • y))
        = dotR y z - (((dotR y y * dotR x z - dotR x y * dotR y z)
            / (dotR x x * dotR y y - dotR x y ^ 2)) * dotR y x
          + ((dotR x x * dotR y z - dotR x y * dotR x z)
            / (dotR x x * dotR y y - dotR x y ^ 2)) * dotR y y) := by
      rw [rw_dotR_sub, rw_dotR_add, rw_dotR_smul, rw_dotR_smul]
    rw [h1, rw_dotR_comm y x]
    have hkey := rw_gram_solve_y (dotR x x) (dotR x y) (dotR y y) (dotR x z) (dotR y z) hΔ
    linarith
  · abel

/-! ## Bilinear forms and the core linear-algebra statement -/

/-- `dotR` is the matrix dot product. -/
@[simp] lemma dotR_eq_dot {ι : Type*} [Fintype ι] (u w : ι → ℝ) : dotR u w = u ⬝ᵥ w := rfl

/-- The rank-one matrix `i j ↦ v i * w j`. -/
def outer {n : ℕ} (v w : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => v i * w j

@[simp] lemma outer_apply {n : ℕ} (v w : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) :
    outer v w i j = v i * w j := rfl

lemma outer_mulVec {n : ℕ} (v w u : Fin (n + 1) → ℝ) :
    (outer v w).mulVec u = (w ⬝ᵥ u) • v := by
  funext i
  simp only [outer, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- The bilinear form `(u,w) ↦ ∑_{i,j} N i j * u i * w j` attached to a matrix `N`. -/
def bf {n : ℕ} (N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (u w : Fin (n + 1) → ℝ) : ℝ :=
  u ⬝ᵥ (N.mulVec w)

lemma bf_add_left {n : ℕ} (N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (u₁ u₂ w) :
    bf N (u₁ + u₂) w = bf N u₁ w + bf N u₂ w := by
  simp only [bf, add_dotProduct]

lemma bf_add_right {n : ℕ} (N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (u w₁ w₂) :
    bf N u (w₁ + w₂) = bf N u w₁ + bf N u w₂ := by
  simp only [bf, Matrix.mulVec_add, dotProduct_add]

lemma bf_smul_left {n : ℕ} (N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (c : ℝ) (u w) :
    bf N (c • u) w = c * bf N u w := by
  simp only [bf, smul_dotProduct, smul_eq_mul]

lemma bf_smul_right {n : ℕ} (N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (c : ℝ) (u w) :
    bf N u (c • w) = c * bf N u w := by
  simp only [bf, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma bf_add_mat {n : ℕ} (N₁ N₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (u w) :
    bf (N₁ + N₂) u w = bf N₁ u w + bf N₂ u w := by
  simp only [bf, Matrix.add_mulVec, dotProduct_add]

lemma bf_smul_mat {n : ℕ} (c : ℝ) (N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (u w) :
    bf (c • N) u w = c * bf N u w := by
  simp only [bf, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma bf_outer {n : ℕ} (v w u u' : Fin (n + 1) → ℝ) :
    bf (outer v w) u u' = (w ⬝ᵥ u') * (u ⬝ᵥ v) := by
  simp only [bf, outer_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_comm]

lemma bf_kill_right {n : ℕ} (N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) {w} (hw : N.mulVec w = 0)
    (u) : bf N u w = 0 := by
  simp only [bf, hw, dotProduct_zero]

lemma bf_symm {n : ℕ} (N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hN : ∀ i j, N i j = N j i)
    (u w) : bf N u w = bf N w u := by
  have hT : Matrix.transpose N = N := by
    funext i j
    rw [Matrix.transpose_apply]
    exact hN j i
  calc bf N u w = u ⬝ᵥ N.mulVec w := rfl
    _ = w ⬝ᵥ (Matrix.transpose N).mulVec u := (Matrix.dotProduct_transpose_mulVec N w u).symm
    _ = w ⬝ᵥ N.mulVec u := by rw [hT]
    _ = bf N w u := rfl

lemma bf_eq_entry {n : ℕ} (N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i j : Fin (n + 1)) :
    bf N (Pi.single i 1) (Pi.single j 1) = N i j := by
  rw [bf, Matrix.dot_mulVec_eq_sum_sum]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, zero_mul, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Pi.single_eq_of_ne hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **The core linear-algebra statement.**  If a symmetric matrix `M` kills the orthogonal
complement of `span {x,y}`, then `M` lies in the span of the three rank-one matrices
`xxᵀ, yyᵀ, (x+y)(x+y)ᵀ`. -/
theorem core {n : ℕ} (x y : Fin (n + 1) → ℝ)
    (hΔ : dotR x x * dotR y y - dotR x y ^ 2 ≠ 0)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hMsym : ∀ i j, M i j = M j i)
    (hker : ∀ v : Fin (n + 1) → ℝ, dotR x v = 0 → dotR y v = 0 → M.mulVec v = 0) :
    ∃ α β γ : ℝ, ∀ i j, M i j
      = α * (x i * x j) + β * (y i * y j) + γ * ((x i + y i) * (x j + y j)) := by
  obtain ⟨α, β, γ, h1, h2, h3⟩ := RW.three_solve (dotR x x) (dotR x y) (dotR y y)
    (bf M x x) (bf M x y) (bf M y y) (by rw [← pow_two]; exact hΔ)
  refine ⟨α, β, γ, fun i j => ?_⟩
  set M' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    α • outer x x + β • outer y y + γ • outer (x + y) (x + y) with hM'def
  have hM'entry : ∀ i j, M' i j
      = α * (x i * x j) + β * (y i * y j) + γ * ((x i + y i) * (x j + y j)) := by
    intro i j
    simp only [hM'def, Matrix.add_apply, Matrix.smul_apply, outer, Pi.add_apply, smul_eq_mul]
  have hM'symm : ∀ i j, M' i j = M' j i := by
    intro i j
    rw [hM'entry i j, hM'entry j i]; ring
  have hform : ∀ u w, bf M' u w = α * (x ⬝ᵥ w) * (u ⬝ᵥ x) + β * (y ⬝ᵥ w) * (u ⬝ᵥ y)
      + γ * ((x + y) ⬝ᵥ w) * (u ⬝ᵥ (x + y)) := by
    intro u w
    rw [hM'def, bf_add_mat, bf_add_mat, bf_smul_mat, bf_smul_mat, bf_smul_mat,
      bf_outer, bf_outer, bf_outer]
    ring
  have hkillM' : ∀ u w, dotR x w = 0 → dotR y w = 0 → bf M' u w = 0 := by
    intro u w hwx hwy
    have hwx' : x ⬝ᵥ w = 0 := hwx
    have hwy' : y ⬝ᵥ w = 0 := hwy
    have hzw : (x + y) ⬝ᵥ w = 0 := by rw [add_dotProduct, hwx', hwy', add_zero]
    rw [hform u w, hwx', hwy', hzw]; ring
  have hxx : bf M x x = bf M' x x := by
    rw [← h1, hform x x]
    simp only [dotR_eq_dot, pow_two, add_dotProduct, dotProduct_add]
    try rw [dotProduct_comm y x]
    ring
  have hxy : bf M x y = bf M' x y := by
    rw [← h2, hform x y]
    simp only [dotR_eq_dot, add_dotProduct, dotProduct_add]
    try rw [dotProduct_comm y x]
    ring
  have hyy : bf M y y = bf M' y y := by
    rw [← h3, hform y y]
    simp only [dotR_eq_dot, pow_two, add_dotProduct, dotProduct_add]
    try rw [dotProduct_comm y x]
    ring
  have hyx : bf M y x = bf M' y x := by
    rw [bf_symm M hMsym y x, bf_symm M' hM'symm y x, hxy]
  have hS : ∀ s, s ∈ Submodule.span ℝ ({x, y} : Set (Fin (n + 1) → ℝ)) →
      ∀ s', s' ∈ Submodule.span ℝ ({x, y} : Set (Fin (n + 1) → ℝ)) →
      bf M s s' = bf M' s s' := by
    intro s hs s' hs'
    rw [Submodule.mem_span_pair] at hs hs'
    obtain ⟨p, q, rfl⟩ := hs
    obtain ⟨p', q', rfl⟩ := hs'
    simp only [bf_add_left, bf_add_right, bf_smul_left, bf_smul_right]
    rw [hxx, hxy, hyx, hyy]
  have key : ∀ u w, bf M u w = bf M' u w := by
    intro u w
    obtain ⟨s, p, hs, hpx, hpy, hzu⟩ := rw_exists_span_add_orth x y u hΔ
    obtain ⟨s', p', hs', hp'x, hp'y, hzw⟩ := rw_exists_span_add_orth x y w hΔ
    rw [hzu, hzw]
    simp only [bf_add_left, bf_add_right]
    have k1 : bf M s p' = 0 := bf_kill_right M (hker p' hp'x hp'y) s
    have k2 : bf M p s' = 0 := by
      rw [bf_symm M hMsym p s']; exact bf_kill_right M (hker p hpx hpy) s'
    have k3 : bf M p p' = 0 := bf_kill_right M (hker p' hp'x hp'y) p
    have k1' : bf M' s p' = 0 := hkillM' s p' hp'x hp'y
    have k2' : bf M' p s' = 0 := by
      rw [bf_symm M' hM'symm p s']; exact hkillM' s' p hpx hpy
    have k3' : bf M' p p' = 0 := hkillM' p p' hp'x hp'y
    simp only [k1, k2, k3, k1', k2', k3', add_zero]
    exact hS s hs s' hs'
  rw [← bf_eq_entry M i j, key, bf_eq_entry M' i j, hM'entry i j]

/-! ## From integer to real orthogonality -/

/-- The kernel condition on the integer points `v ∈ Λ_x ⊓ Λ_y` propagates to all real vectors
orthogonal to `toR x` and `toR y`: the real span of those integer points is the simultaneous real
kernel (`Work.HP.Vero.span_realify_latOrth_inf`). -/
theorem kill_of_integer_orth {n : ℕ} (x y : Fin (n + 1) → ℤ) (a : Mon 2 n → ℝ)
    (h : ∀ (i : Fin (n + 1)) (v : Fin (n + 1) → ℤ), (∑ j, v j * x j = 0) → (∑ j, v j * y j = 0) →
      (∑ j, a (Vero.pairMon n i j) * v j) = 0) :
    ∀ v : Fin (n + 1) → ℝ, dotR (toR x) v = 0 → dotR (toR y) v = 0 →
      ∀ i, (∑ j, a (Vero.pairMon n i j) * v j) = 0 := by
  intro v hvx hvy i
  let L : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun u => ∑ j, a (Vero.pairMon n i j) * u j
      map_add' := by
        intro u u'
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Pi.add_apply, mul_add]
      map_smul' := by
        intro c u
        show (∑ j, a (Vero.pairMon n i j) * (c • u) j)
          = c * ∑ j, a (Vero.pairMon n i j) * u j
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Pi.smul_apply, smul_eq_mul]
        ring }
  have hspan : Submodule.span ℝ ↑(Submodule.map intCastPi (latOrth x ⊓ latOrth y)) ≤ L.ker := by
    rw [Submodule.span_le]
    rintro u hu
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hu
    show (∑ j, a (Vero.pairMon n i j) * (intCastPi w) j) = 0
    have hwx : (∑ j, w j * x j) = 0 := by
      have hw' := hw
      rw [Submodule.mem_inf, latOrth, latOrth, LinearMap.mem_ker, LinearMap.mem_ker,
        Fintype.linearCombination_apply, Fintype.linearCombination_apply] at hw'
      simpa only [smul_eq_mul] using hw'.1
    have hwy : (∑ j, w j * y j) = 0 := by
      have hw' := hw
      rw [Submodule.mem_inf, latOrth, latOrth, LinearMap.mem_ker, LinearMap.mem_ker,
        Fintype.linearCombination_apply, Fintype.linearCombination_apply] at hw'
      simpa only [smul_eq_mul] using hw'.2
    exact h i w hwx hwy
  rw [Vero.span_realify_latOrth_inf x y] at hspan
  have hvmem : v ∈ L.ker := hspan (by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
      rw [show (∑ j, v j • ((x j : ℤ) : ℝ)) = dotR (toR x) v from
        Finset.sum_congr rfl (fun j _ => by simp only [toR, smul_eq_mul]; ring)]
      exact hvx
    · rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
      rw [show (∑ j, v j • ((y j : ℤ) : ℝ)) = dotR (toR y) v from
        Finset.sum_congr rfl (fun j _ => by simp only [toR, smul_eq_mul]; ring)]
      exact hvy)
  change (∑ j, a (Vero.pairMon n i j) * v j) = 0 at hvmem
  exact hvmem

/-! ## The row witness -/

/-- If a real coefficient vector `a : Mon 2 n → ℝ` does not lie in
`V₃ = span_ℝ{ν₂(x), ν₂(y), ν₂(x+y)}`, then some row map `rᵢ(a)` (`(rᵢ a)_j = a (XᵢXⱼ)`, defined as
`rowVecR n i a` in `GamTwoDefs`) pairs nontrivially with a nonzero integer vector orthogonal to
both `x` and `y`.

IMPORTANT: this file must remain importable together with `Submission.Work.HP.Vero`; do not import
`Submission.Work.HP.numaux.Defs`, `DetLOrth`, `det_gam`, `det_gam_gen`, `EElow`, `MDEstimates` or
anything else defining `Work.HP.orthLat` (there is a name clash).

Route (Browning–Le Boudec–Sawin, (Equality sigma)).  Let `Λ := latOrth x ⊓ latOrth y` and
`σ(u,v) ∈ ℤ^{N₂ₙ}` be the coefficient vector of `t ↦ ⟨t,u⟩⟨t,v⟩` (`Vero.sigma`), whose defining
identity is `∑ m, veronese 2 n z m * sigma n u v m = (∑ z_i u_i)(∑ z_j v_j)`
(`Vero.dot_veronese_sigma`).
* `⊆`: for `u : Fin (n+1) → ℤ` and `v ∈ Λ`, `σ(u,v)` is orthogonal to `ν₂(x), ν₂(y)` (both pairings
  involve `⟨x,v⟩ = 0`, `⟨y,v⟩ = 0`) and to `ν₂(x+y)` (`⟨x+y,v⟩ = 0`), so to all of `V₃`.
* `⊇`: `span_ℝ (σ (ℤ^{n+1} × Λ))` has dimension `≥ N₂ₙ - 3`: every `σ(u,u')` with `u = sx+ty+z`,
  `u' = s'x+t'y+z'` (`z,z' ∈ span_ℝ(Λ)`, using `Work.HP.Vero.span_realify_latOrth_inf` to identify
  `span_ℝ(Λ)` and its orthogonal complement) is a combination of `σ(x,x), σ(x,y), σ(y,y)` and terms
  `σ(eᵢ, ·)`; and `span_ℝ{σ(eᵢ,eⱼ) : i,j} = ℝ^{N₂ₙ}` since `σ(eᵢ,eⱼ)` is the standard basis vector
  at `XᵢXⱼ`.  On the other hand `(V₃)^⊥` has dimension `N₂ₙ - 3` provided `ν₂(x), ν₂(y), ν₂(x+y)`
  are independent (a `3×3` minor of the matrix with those three columns is `±(x_jy_i - x_iy_j)³ ≠ 0`,
  via the determinant identity
  `det [[(x_i+y_i)², x_i², y_i²], [(x_i+y_i)(x_j+y_j), x_ix_j, y_iy_j], [(x_j+y_j)², x_j², y_j²]]
   = ±(x_iy_j - x_jy_i)³`).
* Hence if `⟨a, σ(eᵢ,v)⟩ = 0` for all `i, v ∈ Λ` then `a ⊥ span_ℝ(σ(ℤ^{n+1} × Λ)) = (V₃)^⊥`, so
  `a ∈ V₃`, contradiction.
* Finally identify `∑ m, a m * σ(eᵢ,v) m = ∑ j, rowVecR n i a j * v j` (the real analogue of
  `Vero.dot_sigma_rowVec`). -/
theorem RowWitness {n : ℕ} (x y : Fin (n + 1) → ℤ) (hxy : LinearIndependent ℤ ![x, y])
    (a : Mon 2 n → ℝ) (ha : a ∉ V3R n x y) :
    ∃ (i : Fin (n + 1)) (v : Fin (n + 1) → ℤ),
      (∑ j, v j * x j = 0) ∧ (∑ j, v j * y j = 0) ∧
        (∑ j, rowVecR n i a j * v j) ≠ 0 := by
  by_contra hconj
  push_neg at hconj
  apply ha
  have hkill := kill_of_integer_orth x y a (fun i v hvx hvy => by
    simpa only [rowVecR_apply] using hconj i v hvx hvy)
  have hΔ := RW.gramDet_ne_zero hxy
  have hker : ∀ v : Fin (n + 1) → ℝ, dotR (toR x) v = 0 → dotR (toR y) v = 0 →
      Matrix.mulVec (Vero.matA n a) v = 0 := by
    intro v hvx hvy
    funext i
    simpa only [Matrix.mulVec, dotProduct, Vero.matA_apply, Pi.zero_apply]
      using hkill v hvx hvy i
  obtain ⟨α, β, γ, hcombo⟩ := core (toR x) (toR y) hΔ (Vero.matA n a)
    (fun i j => Vero.matA_comm n a i j) hker
  set a' : Mon 2 n → ℝ := α • toR (veronese 2 n x) + β • toR (veronese 2 n y)
    + γ • toR (veronese 2 n (x + y)) with ha'def
  have ha'mem : a' ∈ V3R n x y := by
    rw [V3R]
    exact Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have haeq : a' = a := matA_injective (by
    funext i j
    have h1 : Vero.matA n a' i j = α * Vero.matA n (toR (veronese 2 n x)) i j
        + β * Vero.matA n (toR (veronese 2 n y)) i j
        + γ * Vero.matA n (toR (veronese 2 n (x + y))) i j := by
      rw [ha'def]
      simp only [Pi.add_apply, Pi.smul_apply, Vero.matA_apply, smul_eq_mul]
    rw [h1, matA_veronese x i j, matA_veronese y i j, matA_veronese (x + y) i j, hcombo i j]
    simp only [toR, Pi.add_apply, Int.cast_add])
  exact haeq ▸ ha'mem

end Work.HP.Sig2
