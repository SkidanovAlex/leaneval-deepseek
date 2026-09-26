import Mathlib
import Submission.Work.Radial.quad_iteratedFDeriv_bound
import Submission.Work.Radial.composite_seminorm

namespace Work.Radial

open scoped ContDiff

/-- The number of ordered finpartitions (compositions) of `n` is at most `n!`.
This is the combinatorial input to the sharp Faà-di-Bruno seminorm bound: it replaces the
crude `Fintype.card (OrderedFinpartition n)` constant by `n!`, which is what the target
bound `n! · L · 4^n` needs. -/
lemma card_orderedFinpartition_le_factorial (n : ℕ) :
    Fintype.card (OrderedFinpartition n) ≤ Nat.factorial n := by
  induction n with
  | zero =>
    rw [Fintype.card_unique]
    simp
  | succ n ih =>
    have hcard : Fintype.card (OrderedFinpartition (n+1))
        = ∑ c : OrderedFinpartition n, (c.length + 1) := by
      rw [← Fintype.card_congr (OrderedFinpartition.extendEquiv n)]
      rw [Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro c _
      rw [Fintype.card_option, Fintype.card_fin]
    rw [hcard]
    calc ∑ c : OrderedFinpartition n, (c.length + 1)
        ≤ ∑ _c : OrderedFinpartition n, (n + 1) := by
          apply Finset.sum_le_sum
          intro c _
          have := c.length_le
          omega
      _ = (Fintype.card (OrderedFinpartition n)) * (n + 1) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
      _ ≤ Nat.factorial n * (n + 1) := Nat.mul_le_mul_right _ ih
      _ = Nat.factorial (n + 1) := by rw [Nat.factorial_succ]; ring

theorem profile_seminorm_bound (n : ℕ) [NeZero n] (k l : ℕ) {Ψ : ℝ → ℂ}
    (hΨ : ContDiff ℝ ∞ Ψ) {L : ℝ}
    (hL : ∀ j : ℕ, j ≤ l → ∀ t : ℝ, 0 ≤ t → (1 + t) ^ (k + l) * ‖iteratedDeriv j Ψ t‖ ≤ L) :
    ∀ x : EuclideanSpace ℝ (Fin n),
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun x : EuclideanSpace ℝ (Fin n) => Ψ (‖x‖ ^ 2)) x‖
        ≤ (Nat.factorial l : ℝ) * L * 4 ^ l := by
  intro x
  -- `L` is nonnegative: the `0`-th derivative inequality at `t = 0` reads `‖Ψ 0‖ ≤ L`.
  have hL0 : 0 ≤ L := by
    have h := hL 0 (Nat.zero_le l) 0 (le_refl 0)
    simp only [iteratedDeriv_zero, add_zero, one_pow, one_mul] at h
    exact le_trans (norm_nonneg _) h
  -- Faà di Bruno for `Ψ ∘ (‖·‖²)`.
  have hcomp : iteratedFDeriv ℝ l (fun x : EuclideanSpace ℝ (Fin n) => Ψ (‖x‖ ^ 2)) x
      = (ftaylorSeries ℝ Ψ (‖x‖ ^ 2)).taylorComp
          (ftaylorSeries ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) x) l := by
    have h := iteratedFDeriv_comp (𝕜 := ℝ) (g := Ψ)
      (f := fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2)
      (x := x) (n := ∞) hΨ.contDiffAt (contDiff_norm_sq ℝ).contDiffAt (i := l)
      (WithTop.coe_le_coe.mpr le_top)
    simpa [Function.comp_def] using h
  set B : ℝ := 2 * (1 + ‖x‖) ^ 2 with hBdef
  have hB1 : 1 ≤ B := by
    rw [hBdef]; nlinarith [norm_nonneg x]
  -- Uniform bound on the `q`-terms, from the hypothesis on `Ψ`.
  have hA : ∀ j, j ≤ l →
      ‖ftaylorSeries ℝ Ψ (‖x‖ ^ 2) j‖ ≤ L / (1 + ‖x‖ ^ 2) ^ (k + l) := by
    intro j hj
    rw [show ftaylorSeries ℝ Ψ (‖x‖ ^ 2) j = iteratedFDeriv ℝ j Ψ (‖x‖ ^ 2) from rfl,
        norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact hL j hj (‖x‖ ^ 2) (sq_nonneg _)
  -- Uniform bound on the `p`-terms, from the quadratic nature of `‖·‖²`.
  have hB' : ∀ m, m ≤ l →
      ‖ftaylorSeries ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) x m‖ ≤ B := by
    intro m _
    rw [show ftaylorSeries ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) x m
          = iteratedFDeriv ℝ m (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) x from rfl,
        hBdef]
    exact norm_iteratedFDeriv_norm_sq_le m x
  have hnorm : ‖(ftaylorSeries ℝ Ψ (‖x‖ ^ 2)).taylorComp
        (ftaylorSeries ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) x) l‖
      ≤ (Fintype.card (OrderedFinpartition l) : ℝ) * (L / (1 + ‖x‖ ^ 2) ^ (k + l)) * B ^ l :=
    norm_taylorComp_le l _ B hB1 _ _ hA hB'
  -- `B ^ l ≤ 4 ^ l * (1 + ‖x‖^2) ^ l`.
  have hB_le : B ^ l ≤ 4 ^ l * (1 + ‖x‖ ^ 2) ^ l := by
    rw [hBdef]
    have h1 : (1 + ‖x‖) ^ 2 ≤ 2 * (1 + ‖x‖ ^ 2) := by nlinarith [sq_nonneg (‖x‖ - 1)]
    calc (2 * (1 + ‖x‖) ^ 2) ^ l
        = 2 ^ l * ((1 + ‖x‖) ^ 2) ^ l := by rw [mul_pow]
      _ ≤ 2 ^ l * (2 * (1 + ‖x‖ ^ 2)) ^ l :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 l) (by positivity)
      _ = 2 ^ l * (2 ^ l * (1 + ‖x‖ ^ 2) ^ l) := by rw [mul_pow]
      _ = 4 ^ l * (1 + ‖x‖ ^ 2) ^ l := by
            rw [← mul_assoc, ← mul_pow]; norm_num
  have hmain : ‖x‖ ^ k * B ^ l ≤ 4 ^ l * (1 + ‖x‖ ^ 2) ^ (k + l) := by
    calc ‖x‖ ^ k * B ^ l
        ≤ ‖x‖ ^ k * (4 ^ l * (1 + ‖x‖ ^ 2) ^ l) :=
            mul_le_mul_of_nonneg_left hB_le (by positivity)
      _ = 4 ^ l * (‖x‖ ^ k * (1 + ‖x‖ ^ 2) ^ l) := by ring
      _ ≤ 4 ^ l * ((1 + ‖x‖ ^ 2) ^ k * (1 + ‖x‖ ^ 2) ^ l) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (norm_nonneg x)
                (by nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1/2)]) k) (by positivity)
      _ = 4 ^ l * (1 + ‖x‖ ^ 2) ^ (k + l) := by rw [← pow_add]
  -- The crucial estimate after multiplying by `‖x‖^k` and using the decay of `Ψ`.
  have hDpos : (0 : ℝ) < (1 + ‖x‖ ^ 2) ^ (k + l) := by positivity
  have hkey : ‖x‖ ^ k * ((L / (1 + ‖x‖ ^ 2) ^ (k + l)) * B ^ l) ≤ L * 4 ^ l := by
    have h1 : ‖x‖ ^ k * ((L / (1 + ‖x‖ ^ 2) ^ (k + l)) * B ^ l)
        = (L / (1 + ‖x‖ ^ 2) ^ (k + l)) * (‖x‖ ^ k * B ^ l) := by ring
    rw [h1]
    have h2 : (L / (1 + ‖x‖ ^ 2) ^ (k + l)) * (‖x‖ ^ k * B ^ l)
        ≤ (L / (1 + ‖x‖ ^ 2) ^ (k + l)) * (4 ^ l * (1 + ‖x‖ ^ 2) ^ (k + l)) :=
      mul_le_mul_of_nonneg_left hmain (div_nonneg hL0 (le_of_lt hDpos))
    have h3 : (L / (1 + ‖x‖ ^ 2) ^ (k + l)) * (4 ^ l * (1 + ‖x‖ ^ 2) ^ (k + l))
        = L * 4 ^ l := by
      field_simp
    rwa [h3] at h2
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun x : EuclideanSpace ℝ (Fin n) => Ψ (‖x‖ ^ 2)) x‖
      = ‖x‖ ^ k * ‖(ftaylorSeries ℝ Ψ (‖x‖ ^ 2)).taylorComp
            (ftaylorSeries ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) x) l‖ := by
            rw [hcomp]
    _ ≤ ‖x‖ ^ k * ((Fintype.card (OrderedFinpartition l) : ℝ)
            * ((L / (1 + ‖x‖ ^ 2) ^ (k + l)) * B ^ l)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rwa [mul_assoc] at hnorm
    _ = (Fintype.card (OrderedFinpartition l) : ℝ)
            * (‖x‖ ^ k * ((L / (1 + ‖x‖ ^ 2) ^ (k + l)) * B ^ l)) := by ring
    _ ≤ (Fintype.card (OrderedFinpartition l) : ℝ) * (L * 4 ^ l) :=
            mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (Fintype.card (OrderedFinpartition l) : ℝ) * L * 4 ^ l := by ring
    _ ≤ (Nat.factorial l : ℝ) * L * 4 ^ l := by
            have hc : (Fintype.card (OrderedFinpartition l) : ℝ) ≤ (Nat.factorial l : ℝ) := by
              exact_mod_cast card_orderedFinpartition_le_factorial l
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hL0) (by positivity)

end Work.Radial
