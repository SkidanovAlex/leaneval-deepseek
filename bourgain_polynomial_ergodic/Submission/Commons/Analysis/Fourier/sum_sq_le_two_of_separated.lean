import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Commons.Analysis.Fourier

/-- A finite set of reals that is `2`-separated and lies in the open interval
`(-3/2, 3/2)` has at most two elements. -/
lemma card_le_two_of_separated_real (T : Finset ℝ)
    (hsep : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → 2 ≤ |a - b|)
    (hbd : ∀ a ∈ T, |a| < 3 / 2) : T.card ≤ 2 := by
  refine Finset.card_le_card_of_injOn (fun a : ℝ => if a < 0 then (0 : Fin 2) else 1)
    (fun a _ => Finset.mem_univ _) ?_
  intro a ha b hb hab
  by_cases ha0 : a < 0 <;> by_cases hb0 : b < 0
  · -- both negative: separation forces equality
    by_contra hne
    have hge := hsep a ha b hb hne
    have ha' : -(3 / 2) < a := (abs_lt.mp (hbd a ha)).1
    have hb' : -(3 / 2) < b := (abs_lt.mp (hbd b hb)).1
    have hlt : |a - b| < 3 / 2 := by rw [abs_lt]; constructor <;> linarith
    linarith
  · -- a < 0, b ≥ 0 : the two values in `Fin 2` differ
    simp only [if_pos ha0, if_neg hb0] at hab
    exact absurd hab (by decide)
  · -- a ≥ 0, b < 0 : the two values in `Fin 2` differ
    simp only [if_neg ha0, if_pos hb0] at hab
    exact absurd hab (by decide)
  · -- both nonnegative: separation forces equality
    by_contra hne
    have hge := hsep a ha b hb hne
    have ha'' : a < 3 / 2 := (abs_lt.mp (hbd a ha)).2
    have hb'' : b < 3 / 2 := (abs_lt.mp (hbd b hb)).2
    have ha0' : 0 ≤ a := not_lt.mp ha0
    have hb0' : 0 ≤ b := not_lt.mp hb0
    have hlt : |a - b| < 3 / 2 := by rw [abs_lt]; constructor <;> linarith
    linarith

theorem sum_sq_le_two_of_separated (K : ℕ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (η : ℝ → ℝ) (hη1 : ∀ s : ℝ, |s| ≤ 1 → η s = 1) (hη0 : ∀ s : ℝ, 3 / 2 ≤ |s| → η s = 0)
    (hηnn : ∀ s : ℝ, 0 ≤ η s) (hηle : ∀ s : ℝ, η s ≤ 1) (ξ : ℝ) :
    ∑ k : Fin K, (η (4 * Real.pi * ξ + 2 * lam k)) ^ 2 ≤ 2 := by
  let x : Fin K → ℝ := fun k => 4 * Real.pi * ξ + 2 * lam k
  change ∑ k : Fin K, (η (x k)) ^ 2 ≤ 2
  -- the points `x k` are `2`-separated
  have hxsep : ∀ k l : Fin K, k ≠ l → 2 ≤ |x k - x l| := by
    intro k l hkl
    have h := hsep k l hkl
    have hdiff : x k - x l = 2 * (lam k - lam l) := by
      simp only [x]; ring
    rw [hdiff, abs_mul]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
    nlinarith [abs_nonneg (lam k - lam l)]
  -- each summand is at most `1`
  have hterm : ∀ k : Fin K, (η (x k)) ^ 2 ≤ 1 := by
    intro k
    have h1 : 0 ≤ η (x k) := hηnn (x k)
    have h2 : η (x k) ≤ 1 := hηle (x k)
    nlinarith [sq_nonneg (η (x k))]
  -- the set of indices whose point lies in the open interval `(-3/2, 3/2)`
  set S : Finset (Fin K) := Finset.univ.filter (fun k => |x k| < 3 / 2)
  have hS_zero : ∀ k : Fin K, k ∉ S → (η (x k)) ^ 2 = 0 := by
    intro k hk
    rw [show S = Finset.univ.filter (fun k => |x k| < 3 / 2) from rfl] at hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have hk' : 3 / 2 ≤ |x k| := not_lt.mp hk
    rw [hη0 (x k) hk']
    norm_num
  have h1 : (∑ k : Fin K, (η (x k)) ^ 2) = ∑ k ∈ S, (η (x k)) ^ 2 := by
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun k _ hk => hS_zero k hk)]
  have h2 : ∑ k ∈ S, (η (x k)) ^ 2 ≤ (S.card : ℝ) := by
    calc ∑ k ∈ S, (η (x k)) ^ 2 ≤ ∑ k ∈ S, (1 : ℝ) :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ = (S.card : ℝ) := by simp
  have h3 : S.card ≤ 2 := by
    have hinj : Set.InjOn x ↑S := by
      intro k _ l _ hkl
      by_contra hne
      have hge := hxsep k l hne
      have h0 : |x k - x l| = 0 := by rw [hkl]; simp
      linarith
    have himg : (S.image x).card = S.card := Finset.card_image_of_injOn hinj
    rw [← himg]
    refine card_le_two_of_separated_real (S.image x) ?_ ?_
    · intro a ha b hb hab
      rw [Finset.mem_image] at ha hb
      obtain ⟨k, _, rfl⟩ := ha
      obtain ⟨l, _, rfl⟩ := hb
      exact hxsep k l (fun hkl => hab (by rw [hkl]))
    · intro a ha
      rw [Finset.mem_image] at ha
      obtain ⟨k, hk, rfl⟩ := ha
      have hk' : |x k| < 3 / 2 := by
        rw [show S = Finset.univ.filter (fun k => |x k| < 3 / 2) from rfl] at hk
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hk
      exact hk'
  calc (∑ k : Fin K, (η (x k)) ^ 2) = ∑ k ∈ S, (η (x k)) ^ 2 := h1
    _ ≤ (S.card : ℝ) := h2
    _ ≤ 2 := by exact_mod_cast h3

end Commons.Analysis.Fourier