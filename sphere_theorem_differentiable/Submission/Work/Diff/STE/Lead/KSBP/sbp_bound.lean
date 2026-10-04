import Mathlib
import Submission.Work.Diff.STE.Lead.KSBP.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The summation-by-parts bound for the Friedrichs truncation kernel

This file proves `Work.Diff.STE.Lead.KSBP.sbp_bound`: for a finitely supported coefficient
family `a : (Fin n → ℤ) → ℂ` and a list `l` of coordinates at which the character
`e^{2πi xᵢ}` is not `1`, the value of the Fourier series at `x` is bounded by the product of
the inverse squared SBP factors `‖e^{2πi xᵢ} - 1‖^{-2}` times the `ℓ¹` norm of the iterated
second difference `diffL l a`.

The argument is the classical one: the second difference `diff2 i` is the Fourier multiplier
`(e^{2πi xᵢ} - 1)²` (up to the convention on the shift), i.e.

  `∑'_m (diff2 i b) m · χ_m(x) = (χ_{eᵢ}(x) - 1)² · ∑'_m b m · χ_m(x)`,

where `χ_m(x) = fourierExp m x` is a character.  Iterating over `l` and taking norms gives the
claim, the sum on the right being bounded by the triangle inequality (all characters have norm
one).
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.Lead.KSBP

variable {n : ℕ}

/-! ### Elementary properties of the characters -/

/-- `fourierExp` is multiplicative in the index. -/
lemma sbp_fourierExp_add (m c : Fin n → ℤ) (x : Fin n → ℝ) :
    Work.Diff.STE.fourierExp (m + c) x
      = Work.Diff.STE.fourierExp m x * Work.Diff.STE.fourierExp c x := by
  rw [Work.Diff.STE.fourierExp, Work.Diff.STE.fourierExp, Work.Diff.STE.fourierExp,
    ← Complex.exp_add]
  congr 1
  have h : (∑ i, (((m + c) i : ℤ) : ℂ) * (x i : ℂ))
      = (∑ i, ((m i : ℤ) : ℂ) * (x i : ℂ)) + ∑ i, ((c i : ℤ) : ℂ) * (x i : ℂ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by simp only [Pi.add_apply, Int.cast_add]; ring)
  rw [h]; ring

/-- The character at a single unit basis vector is `e^{2πi xᵢ}`. -/
lemma sbp_fourierExp_single (i : Fin n) (x : Fin n → ℝ) :
    Work.Diff.STE.fourierExp (Pi.single i (1 : ℤ)) x
      = Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) := by
  rw [Work.Diff.STE.fourierExp]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_eq_of_ne hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- Every character has norm one. -/
lemma sbp_norm_fourierExp (m : Fin n → ℤ) (x : Fin n → ℝ) :
    ‖Work.Diff.STE.fourierExp m x‖ = 1 := by
  have hmain : (2 * (Real.pi : ℂ) * Complex.I * ∑ i, ((m i : ℤ) : ℂ) * (x i : ℂ))
      = (((2 * Real.pi * ∑ i, ((m i : ℤ) : ℝ) * x i : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  rw [Work.Diff.STE.fourierExp, hmain, Complex.norm_exp_ofReal_mul_I]

/-! ### Shifting the summation index -/

/-- Shifting the index of a character series by `c` multiplies the value by `χ_c(x)`. -/
lemma sbp_tsum_shift (x : Fin n → ℝ) (c : Fin n → ℤ) (b : (Fin n → ℤ) → ℂ) :
    ∑' m, b (m - c) * Work.Diff.STE.fourierExp m x
      = Work.Diff.STE.fourierExp c x * ∑' m, b m * Work.Diff.STE.fourierExp m x := by
  have h1 : (∑' m, b (m - c) * Work.Diff.STE.fourierExp m x)
      = ∑' m, b m * Work.Diff.STE.fourierExp (m + c) x := by
    have := Equiv.tsum_eq (Equiv.subRight c)
      (fun m => b m * Work.Diff.STE.fourierExp (m + c) x)
    simpa only [Equiv.subRight_apply, sub_add_cancel] using this
  rw [h1]
  have h2 : (∑' m, b m * Work.Diff.STE.fourierExp (m + c) x)
      = ∑' m, (b m * Work.Diff.STE.fourierExp m x) * Work.Diff.STE.fourierExp c x :=
    tsum_congr (fun m => by rw [sbp_fourierExp_add]; ring)
  rw [h2, tsum_mul_right, mul_comm]

/-- Summability is preserved by a shift of the index. -/
lemma sbp_summable_shift (x : Fin n → ℝ) (c : Fin n → ℤ) {b : (Fin n → ℤ) → ℂ}
    (hb : Summable (fun m => b m * Work.Diff.STE.fourierExp m x)) :
    Summable (fun m => b (m - c) * Work.Diff.STE.fourierExp m x) := by
  have h1 : Summable (fun m => b m * Work.Diff.STE.fourierExp (m + c) x) :=
    (summable_congr (fun m => by rw [sbp_fourierExp_add]; ring)).mpr (hb.mul_right _)
  have h2 : Summable (fun m => b ((Equiv.subRight c) m)
        * Work.Diff.STE.fourierExp ((Equiv.subRight c) m + c) x) :=
    (Equiv.summable_iff (Equiv.subRight c)).mpr h1
  refine (summable_congr (fun m => ?_)).mp h2
  simp only [Equiv.subRight_apply, sub_add_cancel]

/-! ### The second difference as a Fourier multiplier -/

/-- The second difference `diff2 i` acts on the series of `b` by multiplication by
`(χ_{eᵢ}(x) - 1)²`. -/
lemma sbp_summable_tsum_diff2 (x : Fin n → ℝ) (i : Fin n) {b : (Fin n → ℤ) → ℂ}
    (hb : Summable (fun m => b m * Work.Diff.STE.fourierExp m x)) :
    Summable (fun m => diff2 i b m * Work.Diff.STE.fourierExp m x) ∧
      ∑' m, diff2 i b m * Work.Diff.STE.fourierExp m x
        = (Work.Diff.STE.fourierExp (Pi.single i (1 : ℤ)) x - 1) ^ 2
          * ∑' m, b m * Work.Diff.STE.fourierExp m x := by
  set e : Fin n → ℤ := Pi.single i (1 : ℤ) with he
  set c2 : Fin n → ℤ := (2 : ℤ) • e with hc2
  have hu : Summable (fun m => b (m - c2) * Work.Diff.STE.fourierExp m x) :=
    sbp_summable_shift x c2 hb
  have hv : Summable (fun m => b (m - e) * Work.Diff.STE.fourierExp m x) :=
    sbp_summable_shift x e hb
  have h2v : Summable (fun m => (2 : ℂ) * (b (m - e) * Work.Diff.STE.fourierExp m x)) :=
    hv.mul_left 2
  have hpt : ∀ m, diff2 i b m * Work.Diff.STE.fourierExp m x
      = b (m - c2) * Work.Diff.STE.fourierExp m x
        + (b m * Work.Diff.STE.fourierExp m x
            - (2 : ℂ) * (b (m - e) * Work.Diff.STE.fourierExp m x)) := by
    intro m; simp only [diff2, hc2, he]; ring
  constructor
  · exact (summable_congr hpt).mpr (hu.add (hb.sub h2v))
  · have hc2e : c2 = e + e := by rw [hc2]; exact two_smul ℤ e
    have hfc2 : Work.Diff.STE.fourierExp c2 x = Work.Diff.STE.fourierExp e x ^ 2 := by
      rw [hc2e, sbp_fourierExp_add]; ring
    calc ∑' m, diff2 i b m * Work.Diff.STE.fourierExp m x
        = ∑' m, (b (m - c2) * Work.Diff.STE.fourierExp m x
            + (b m * Work.Diff.STE.fourierExp m x
                - (2 : ℂ) * (b (m - e) * Work.Diff.STE.fourierExp m x))) :=
          tsum_congr hpt
      _ = (∑' m, b (m - c2) * Work.Diff.STE.fourierExp m x)
            + (∑' m, b m * Work.Diff.STE.fourierExp m x
                - ∑' m, (2 : ℂ) * (b (m - e) * Work.Diff.STE.fourierExp m x)) := by
          rw [Summable.tsum_add hu (hb.sub h2v), Summable.tsum_sub hb h2v]
      _ = (Work.Diff.STE.fourierExp c2 x * ∑' m, b m * Work.Diff.STE.fourierExp m x)
            + (∑' m, b m * Work.Diff.STE.fourierExp m x
                - 2 * (Work.Diff.STE.fourierExp e x
                    * ∑' m, b m * Work.Diff.STE.fourierExp m x)) := by
          rw [sbp_tsum_shift x c2 b, tsum_mul_left, sbp_tsum_shift x e b]
      _ = (Work.Diff.STE.fourierExp e x - 1) ^ 2
            * ∑' m, b m * Work.Diff.STE.fourierExp m x := by
          rw [hfc2]; ring

/-! ### The iterated second difference -/

/-- A finitely supported family is summable against any character. -/
lemma sbp_summable_of_support_finite {a : (Fin n → ℤ) → ℂ}
    (h : (Function.support a).Finite) (x : Fin n → ℝ) :
    Summable (fun m => a m * Work.Diff.STE.fourierExp m x) := by
  refine summable_of_hasFiniteSupport (h.subset ?_)
  intro m hm
  rw [Function.mem_support] at hm ⊢
  exact fun h0 => hm (by simp [h0])

/-- Iterating the second-difference identity over a list of coordinates. -/
lemma sbp_summable_tsum_diffL (a : (Fin n → ℤ) → ℂ) (hfin : (Function.support a).Finite)
    (l : List (Fin n)) (x : Fin n → ℝ) :
    Summable (fun m => diffL l a m * Work.Diff.STE.fourierExp m x) ∧
      ∑' m, diffL l a m * Work.Diff.STE.fourierExp m x
        = (l.map (fun i => (Work.Diff.STE.fourierExp (Pi.single i (1 : ℤ)) x - 1) ^ 2)).prod
            * ∑' m, a m * Work.Diff.STE.fourierExp m x := by
  induction l with
  | nil =>
      constructor
      · exact sbp_summable_of_support_finite hfin x
      · simp [diffL]
  | cons i t ih =>
      obtain ⟨hsum_t, htsum_t⟩ := ih
      obtain ⟨hsum_d, htsum_d⟩ := sbp_summable_tsum_diff2 x i hsum_t
      have hd : diffL (i :: t) a = diff2 i (diffL t a) := rfl
      constructor
      · rwa [hd]
      · rw [hd, htsum_d, htsum_t, List.map_cons, List.prod_cons]
        ring

/-! ### Norms of products -/

lemma sbp_norm_prod_map {α : Type*} (l : List α) (f : α → ℂ) :
    ‖(l.map f).prod‖ = (l.map (fun i => ‖f i‖)).prod := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.map_cons, List.prod_cons, ih]

lemma sbp_prod_map_inv {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map (fun i => (f i)⁻¹)).prod = ((l.map f).prod)⁻¹ := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ih, mul_inv]

/-- The product of the squared SBP factors is nonzero as soon as no factor vanishes. -/
lemma sbp_prod_map_sq_ne_zero {l : List (Fin n)} {x : Fin n → ℝ}
    (hx : ∀ i ∈ l, Work.Diff.STE.fourierExp (Pi.single i (1 : ℤ)) x ≠ 1) :
    (l.map (fun i => (Work.Diff.STE.fourierExp (Pi.single i (1 : ℤ)) x - 1) ^ 2)).prod ≠ 0 := by
  induction l with
  | nil => simp
  | cons i t ih =>
      rw [List.map_cons, List.prod_cons]
      have hi : Work.Diff.STE.fourierExp (Pi.single i (1 : ℤ)) x - 1 ≠ 0 :=
        sub_ne_zero.mpr (hx i (by simp))
      exact mul_ne_zero (pow_ne_zero 2 hi) (ih (fun j hj => hx j (by simp [hj])))

/-! ### The bound -/

theorem sbp_bound {n : ℕ} (a : (Fin n → ℤ) → ℂ) (l : List (Fin n)) (x : Fin n → ℝ)
    (hfin : (Function.support a).Finite)
    (hx : ∀ i ∈ l, Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) ≠ 1) :
    ‖∑' m : Fin n → ℤ, a m * Work.Diff.STE.fourierExp m x‖
      ≤ (l.map (fun i => (‖Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1‖ ^ 2)⁻¹)).prod
        * ∑' m : Fin n → ℤ, ‖Work.Diff.STE.Lead.KSBP.diffL l a m‖ := by
  obtain ⟨hsum, htsum⟩ := sbp_summable_tsum_diffL a hfin l x
  set S : ℂ := ∑' m : Fin n → ℤ, a m * Work.Diff.STE.fourierExp m x with hS
  set G : ℝ :=
    (l.map (fun i => (‖Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1‖ ^ 2)⁻¹)).prod
      with hG
  set T : ℝ := ∑' m : Fin n → ℤ, ‖Work.Diff.STE.Lead.KSBP.diffL l a m‖ with hT
  have hPne :
      (l.map (fun i => (Work.Diff.STE.fourierExp (Pi.single i (1 : ℤ)) x - 1) ^ 2)).prod ≠ 0 := by
    refine sbp_prod_map_sq_ne_zero ?_
    intro i hi; rw [sbp_fourierExp_single]; exact hx i hi
  have hS_eq : S
      = (l.map (fun i => (Work.Diff.STE.fourierExp (Pi.single i (1 : ℤ)) x - 1) ^ 2)).prod⁻¹
        * (∑' m, Work.Diff.STE.Lead.KSBP.diffL l a m * Work.Diff.STE.fourierExp m x) := by
    rw [hS, htsum]
    exact (inv_mul_cancel_left₀ hPne (∑' m, a m * Work.Diff.STE.fourierExp m x)).symm
  have hSd_bound :
      ‖∑' m, Work.Diff.STE.Lead.KSBP.diffL l a m * Work.Diff.STE.fourierExp m x‖ ≤ T := by
    rw [hT]
    calc ‖∑' m, Work.Diff.STE.Lead.KSBP.diffL l a m * Work.Diff.STE.fourierExp m x‖
        ≤ ∑' m, ‖Work.Diff.STE.Lead.KSBP.diffL l a m * Work.Diff.STE.fourierExp m x‖ :=
          norm_tsum_le_tsum_norm hsum.norm
      _ = ∑' m, ‖Work.Diff.STE.Lead.KSBP.diffL l a m‖ :=
          tsum_congr (fun m => by rw [norm_mul, sbp_norm_fourierExp, mul_one])
  have hmap : (l.map (fun i => (Work.Diff.STE.fourierExp (Pi.single i (1 : ℤ)) x - 1) ^ 2))
      = (l.map (fun i => (Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1) ^ 2)) :=
    List.map_congr_left (fun i _ => by rw [sbp_fourierExp_single])
  have hPG :
      ‖((l.map (fun i => (Work.Diff.STE.fourierExp (Pi.single i (1 : ℤ)) x - 1) ^ 2)).prod)⁻¹‖
        = G := by
    rw [hG, hmap, norm_inv, sbp_norm_prod_map, ← sbp_prod_map_inv]
    exact congrArg List.prod (List.map_congr_left (fun i _ => by rw [norm_pow]))
  have step : ‖S‖ ≤
      ‖((l.map (fun i => (Work.Diff.STE.fourierExp (Pi.single i (1 : ℤ)) x - 1) ^ 2)).prod)⁻¹‖
        * T := by
    rw [hS_eq, norm_mul]
    exact mul_le_mul_of_nonneg_left hSd_bound (norm_nonneg _)
  rw [hPG] at step
  exact step

end Work.Diff.STE.Lead.KSBP
