import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

/-- Pointwise algebraic estimate behind the far bound: for `|x| ≤ 1` and reals `a`, `b`,
`(x * a + (x - 1) * b)^2 ≤ 3 * a^2 + 6 * b^2`.

(With `x = χ t`, `a = G t - c t`, `b = c t` this gives
`(χ t * G t - c t)^2 ≤ 3 * (G t - c t)^2 + 6 * (c t)^2`.) -/
private lemma farPointwise {x a b : ℝ} (hx : |x| ≤ 1) :
    (x * a + (x - 1) * b) ^ 2 ≤ 3 * a ^ 2 + 6 * b ^ 2 := by
  have hx1 : x ≤ 1 := (abs_le.mp hx).2
  have hx0 : -1 ≤ x := (abs_le.mp hx).1
  have hA : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x, hx]
  have hB : (x - 1) ^ 2 ≤ 4 := by nlinarith [hx0, hx1]
  have hy : |x * (x - 1)| ≤ 2 := by
    rw [abs_mul]
    have h2 : |x - 1| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    simpa using mul_le_mul hx h2 (abs_nonneg _) zero_le_one
  have hy1 : x * (x - 1) ≤ 2 := (abs_le.mp hy).2
  have hy2 : -2 ≤ x * (x - 1) := (abs_le.mp hy).1
  have hC : 2 * (x * (x - 1)) * a * b ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    have h1 : 0 ≤ 1 - (x * (x - 1)) / 2 := by linarith
    have h2 : 0 ≤ 1 + (x * (x - 1)) / 2 := by linarith
    have hcert : 2 * a ^ 2 + 2 * b ^ 2 - 2 * (x * (x - 1)) * a * b
        = (1 - (x * (x - 1)) / 2) * (a + b) ^ 2
          + (1 + (x * (x - 1)) / 2) * (a - b) ^ 2 := by
      ring
    have : 0 ≤ 2 * a ^ 2 + 2 * b ^ 2 - 2 * (x * (x - 1)) * a * b := by
      rw [hcert]
      exact add_nonneg (mul_nonneg h1 (sq_nonneg _)) (mul_nonneg h2 (sq_nonneg _))
    linarith
  nlinarith [hA, hB, hC, sq_nonneg a, sq_nonneg b]

theorem far_bound {c G χ : ℝ → ℝ} {r N ε₁ η : ℝ}
    (hr : 0 < r) (hr1 : 2 * r ≤ 1) (hN : 2 ≤ N)
    (hχ0 : ∀ t : ℝ, N ≤ t → χ t = 0)
    (hχ1 : ∀ t : ℝ, r ≤ t → t ≤ N / 2 → χ t = 1)
    (hχb : ∀ t : ℝ, |χ t| ≤ 1)
    (hcH : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1))
    (hη : ∫ t in Set.Ioi (N / 2), (c t) ^ 2 ≤ η)
    (hGint : MeasureTheory.IntegrableOn (fun t : ℝ => (G t - c t) ^ 2) (Set.Icc (r / 2) (2 * N)))
    (happ : ∫ t in Set.Icc (r / 2) (2 * N), (G t - c t) ^ 2 ≤ ε₁)
    (hint : MeasureTheory.IntegrableOn (fun t : ℝ => (χ t * G t - c t) ^ 2) (Set.Ioi 1)) :
    ∫ t in Set.Ioi 1, (χ t * G t - c t) ^ 2 ≤ 5 * ε₁ + 7 * η := by
  -- `r ≤ 1/2 < 1 ≤ N/2 ≤ N`
  have hN1 : (1:ℝ) ≤ N / 2 := by linarith
  have hN2 : (N:ℝ) / 2 ≤ N := by linarith
  have hr2 : r ≤ 1 / 2 := by linarith
  -- the two "small quantities" are nonnegative
  have hε₁ : 0 ≤ ε₁ :=
    le_trans (MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun x _ => sq_nonneg _)) happ
  -- Split `Ioi 1 = Ioc 1 (N/2) ∪ Ioi (N/2)`.
  have hsplit : (∫ t in Set.Ioi 1, (χ t * G t - c t) ^ 2)
      = (∫ t in Set.Ioc 1 (N / 2), (χ t * G t - c t) ^ 2)
        + (∫ t in Set.Ioi (N / 2), (χ t * G t - c t) ^ 2) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hN1]
    exact MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi (le_refl (N / 2))) measurableSet_Ioi
      (hint.mono_set Set.Ioc_subset_Ioi_self)
      (hint.mono_set (Set.Ioi_subset_Ioi hN1))
  -- Split `Ioi (N/2) = Ioc (N/2) N ∪ Ioi N`.
  have hsplit2 : (∫ t in Set.Ioi (N / 2), (χ t * G t - c t) ^ 2)
      = (∫ t in Set.Ioc (N / 2) N, (χ t * G t - c t) ^ 2)
        + (∫ t in Set.Ioi N, (χ t * G t - c t) ^ 2) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hN2]
    exact MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi (le_refl N)) measurableSet_Ioi
      (hint.mono_set ((Set.Ioc_subset_Ioc hN1 (le_refl N)).trans Set.Ioc_subset_Ioi_self))
      (hint.mono_set (Set.Ioi_subset_Ioi (by linarith : (1:ℝ) ≤ N)))
  -- Region 1: `χ = 1`, so the integrand is `(G - c)^2`.
  have hA : (∫ t in Set.Ioc 1 (N / 2), (χ t * G t - c t) ^ 2) ≤ ε₁ := by
    have hcongr : (∫ t in Set.Ioc 1 (N / 2), (χ t * G t - c t) ^ 2)
        = (∫ t in Set.Ioc 1 (N / 2), (G t - c t) ^ 2) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun x hx => by
        have hx' : 1 < x ∧ x ≤ N / 2 := hx
        have hxr : r ≤ x := by linarith [hx'.1]
        rw [hχ1 x hxr hx'.2]
        ring)
    rw [hcongr]
    have hsubA : Set.Ioc 1 (N / 2) ⊆ Set.Icc (r / 2) (2 * N) := fun x hx => by
      simp only [Set.mem_Ioc] at hx
      simp only [Set.mem_Icc]
      exact ⟨by linarith [hx.1], by linarith [hx.2, hN]⟩
    have hmono : (∫ t in Set.Ioc 1 (N / 2), (G t - c t) ^ 2)
        ≤ (∫ t in Set.Icc (r / 2) (2 * N), (G t - c t) ^ 2) :=
      MeasureTheory.setIntegral_mono_set hGint
        (Filter.Eventually.of_forall (fun x => sq_nonneg (G x - c x)))
        (Filter.Eventually.of_forall (fun x hx => hsubA hx))
    linarith [happ]
  -- Region 3: `χ = 0`, so the integrand is `c^2`.
  have hC : (∫ t in Set.Ioi N, (χ t * G t - c t) ^ 2) ≤ η := by
    have hcongr : (∫ t in Set.Ioi N, (χ t * G t - c t) ^ 2)
        = (∫ t in Set.Ioi N, (c t) ^ 2) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
        rw [hχ0 x (le_of_lt hx)]
        ring)
    rw [hcongr]
    have hcIoiN2 : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi (N / 2)) :=
      hcH.mono_set (Set.Ioi_subset_Ioi hN1)
    have hsubC : Set.Ioi N ⊆ Set.Ioi (N / 2) := Set.Ioi_subset_Ioi hN2
    have hmono : (∫ t in Set.Ioi N, (c t) ^ 2) ≤ (∫ t in Set.Ioi (N / 2), (c t) ^ 2) :=
      MeasureTheory.setIntegral_mono_set hcIoiN2
        (Filter.Eventually.of_forall (fun x => sq_nonneg (c x)))
        (Filter.Eventually.of_forall (fun x hx => hsubC hx))
    linarith [hη]
  -- Region 2: only `|χ| ≤ 1` is known, giving `≤ 3 (G-c)^2 + 6 c^2` pointwise.
  have hB : (∫ t in Set.Ioc (N / 2) N, (χ t * G t - c t) ^ 2) ≤ 3 * ε₁ + 6 * η := by
    have hsub1 : Set.Ioc (N / 2) N ⊆ Set.Icc (r / 2) (2 * N) := fun x hx => by
      simp only [Set.mem_Ioc] at hx
      simp only [Set.mem_Icc]
      exact ⟨by linarith [hx.1], by linarith [hx.2, hN]⟩
    have hsub2 : Set.Ioc (N / 2) N ⊆ Set.Ioi 1 := fun x hx => by
      simp only [Set.mem_Ioc] at hx
      simp only [Set.mem_Ioi]
      linarith [hx.1, hN1]
    have hsub3 : Set.Ioc (N / 2) N ⊆ Set.Ioi (N / 2) := fun x hx => by
      simp only [Set.mem_Ioc] at hx
      simp only [Set.mem_Ioi]
      exact hx.1
    have hGs : MeasureTheory.IntegrableOn (fun t : ℝ => (G t - c t) ^ 2) (Set.Ioc (N / 2) N) :=
      hGint.mono_set hsub1
    have hcs : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioc (N / 2) N) :=
      hcH.mono_set hsub2
    have hfs : MeasureTheory.IntegrableOn (fun t : ℝ => (χ t * G t - c t) ^ 2)
        (Set.Ioc (N / 2) N) :=
      hint.mono_set hsub2
    have hgs : MeasureTheory.IntegrableOn (fun t : ℝ => 3 * (G t - c t) ^ 2 + 6 * (c t) ^ 2)
        (Set.Ioc (N / 2) N) :=
      (hGs.integrable.const_mul 3).add (hcs.integrable.const_mul 6)
    have hle : (∫ t in Set.Ioc (N / 2) N, (χ t * G t - c t) ^ 2)
        ≤ (∫ t in Set.Ioc (N / 2) N, (3 * (G t - c t) ^ 2 + 6 * (c t) ^ 2)) :=
      MeasureTheory.setIntegral_mono_on hfs hgs measurableSet_Ioc (fun x hx => by
        have heq : χ x * (G x - c x) + (χ x - 1) * c x = χ x * G x - c x := by ring
        rw [← heq]
        exact farPointwise (hχb x))
    have heq2 : (∫ t in Set.Ioc (N / 2) N, (3 * (G t - c t) ^ 2 + 6 * (c t) ^ 2))
        = 3 * (∫ t in Set.Ioc (N / 2) N, (G t - c t) ^ 2)
          + 6 * (∫ t in Set.Ioc (N / 2) N, (c t) ^ 2) := by
      rw [MeasureTheory.integral_add (hGs.integrable.const_mul 3) (hcs.integrable.const_mul 6),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hGle : (∫ t in Set.Ioc (N / 2) N, (G t - c t) ^ 2) ≤ ε₁ := by
      have hmono := MeasureTheory.setIntegral_mono_set hGint
        (Filter.Eventually.of_forall (fun x => sq_nonneg (G x - c x)))
        (Filter.Eventually.of_forall (fun x hx => hsub1 hx))
      linarith [happ]
    have hcle : (∫ t in Set.Ioc (N / 2) N, (c t) ^ 2) ≤ η := by
      have hcIoiN2 : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi (N / 2)) :=
        hcH.mono_set (Set.Ioi_subset_Ioi hN1)
      have hmono := MeasureTheory.setIntegral_mono_set hcIoiN2
        (Filter.Eventually.of_forall (fun x => sq_nonneg (c x)))
        (Filter.Eventually.of_forall (fun x hx => hsub3 hx))
      linarith [hη]
    linarith [hle, heq2, hGle, hcle]
  linarith [hsplit, hsplit2, hA, hB, hC, hε₁]

end Work.FTS.PhiStar.Honesty
