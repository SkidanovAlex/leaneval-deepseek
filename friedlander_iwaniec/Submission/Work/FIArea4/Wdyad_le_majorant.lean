import Mathlib
import Submission.Work.FIArea4.WdyadSetup

/-!
# Bounding the dyadic dual variance `Wdyad` by the Gaussian majorant

`Work.FIArea4.Wdyad_le_majorant` states that the dyadic dual variance
`Wdyad D R S γ` (a sum over the box `R < r ≤ 2R`, `S < s ≤ 2S`) is bounded by the
full `ℤ`-sum of the rapidly decaying Gaussian majorant `gmajor (S:ℝ) (s:ℝ)` times the
squared modulus of the class sum `TZ D R S γ r s`.

The point of the estimate is that `gmajor (S:ℝ) ≥ 1` on `(S, 2S]`, so replacing the sharp
`s`-interval `(S, 2S]` by the whole integer line weighted by `gmajor` only enlarges the sum;
the resulting `∑' s : ℤ` is amenable to Poisson summation (`WdyadPoisson.lean`).

Everything here is elementary: the only analytic input is that the Gaussian `gmajor σ`
is summable on `ℤ`.
-/

namespace Work.FIArea4

open Finset
open scoped BigOperators

noncomputable section

/-! ## The class sum with integer `s` agrees with the natural one -/

/-- The integer version of the matrix entry agrees with the natural one on natural inputs. -/
lemma MentryZ_ofNat (d a r s : ℕ) : MentryZ d a r (s : ℤ) = Mentry d a r s := by
  unfold MentryZ Mentry
  simp

/-- The integer class sum `TZ` at a natural index is the class sum appearing in `Wdyad`. -/
lemma TZ_ofNat (D R S : ℕ) (γ : ℕ → ℕ → ℂ) (r s : ℕ) :
    TZ D R S γ r (s : ℤ) =
      ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, γ a d * Mentry d a r s := by
  unfold TZ
  simp only [MentryZ_ofNat]

/-! ## A uniform bound for `TZ`

`MentryZ` is a product of an indicator and a Jacobi symbol, hence of modulus at most `1`;
therefore `TZ D R S γ r s` is uniformly bounded in `s` by `∑ ‖γ a d‖`. -/

lemma norm_jacobiSym_cast_le_one (a : ℤ) (b : ℕ) : ‖((jacobiSym a b : ℤ) : ℂ)‖ ≤ 1 := by
  rcases jacobiSym.trichotomy a b with h | h | h <;> rw [h] <;> norm_num

lemma norm_MentryZ_le_one (d a r : ℕ) (s : ℤ) : ‖MentryZ d a r s‖ ≤ 1 := by
  unfold MentryZ
  split
  · exact norm_jacobiSym_cast_le_one _ _
  · simp

/-- Uniform bound for the class sum `TZ` (independent of `s`). -/
lemma norm_TZ_le (D R S : ℕ) (γ : ℕ → ℕ → ℂ) (r : ℕ) (s : ℤ) :
    ‖TZ D R S γ r s‖ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, ‖γ a d‖ := by
  unfold TZ
  calc ‖∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, γ a d * MentryZ d a r s‖
      ≤ ∑ d ∈ Finset.Ioc D (2 * D), ‖∑ a ∈ Finset.range d, γ a d * MentryZ d a r s‖ :=
        norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, ‖γ a d * MentryZ d a r s‖ :=
        Finset.sum_le_sum (fun d _ => norm_sum_le _ _)
    _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, ‖γ a d‖ := by
        apply Finset.sum_le_sum; intro d _
        apply Finset.sum_le_sum; intro a _
        rw [norm_mul]
        calc ‖γ a d‖ * ‖MentryZ d a r s‖ ≤ ‖γ a d‖ * 1 :=
              mul_le_mul_of_nonneg_left (norm_MentryZ_le_one d a r s) (norm_nonneg _)
          _ = ‖γ a d‖ := mul_one _

/-- Squared-modulus version of the uniform bound: `normSq (TZ …) ≤ (∑ ‖γ a d‖)²`. -/
lemma normSq_TZ_le (D R S : ℕ) (γ : ℕ → ℕ → ℂ) (r : ℕ) (s : ℤ) :
    Complex.normSq (TZ D R S γ r s)
      ≤ (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, ‖γ a d‖) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_TZ_le D R S γ r s) 2

/-! ## Summability of the Gaussian majorant on `ℤ` -/

/-- `s ↦ exp (-d * s²)` is summable on `ℤ` for `d > 0`. -/
lemma summable_exp_neg_sq_int {d : ℝ} (hd : 0 < d) :
    Summable (fun s : ℤ => Real.exp (-d * (s : ℝ) ^ 2)) := by
  apply Summable.of_nat_of_neg_add_one
  · have h := Real.summable_exp_nat_mul_of_ge (c := -d) (by linarith)
      (f := fun i : ℕ => (i : ℝ) ^ 2) (fun i => by
        rcases i with _ | j
        · simp
        · push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) j])
    simpa using h
  · have h := Real.summable_exp_nat_mul_of_ge (c := -d) (by linarith)
      (f := fun i : ℕ => ((i : ℝ) + 1) ^ 2) (fun i => by
        nlinarith [Nat.cast_nonneg (α := ℝ) i])
    rw [show (fun n : ℕ => (fun s : ℤ => Real.exp (-d * (s : ℝ) ^ 2)) (-(↑n + 1)))
        = (fun n : ℕ => Real.exp (-d * ((n : ℝ) + 1) ^ 2)) by
      funext n; push_cast; congr 1; ring]
    exact h

/-- The Gaussian majorant is dominated by a pure Gaussian `exp (5π/2) * exp (-π x²/(2σ²))`. -/
lemma gmajor_le_exp_neg {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    gmajor σ x ≤ Real.exp (5 * Real.pi / 2) * Real.exp (-(Real.pi) * x ^ 2 / (2 * σ ^ 2)) := by
  have h2 : (x - 3 * σ / 2) ^ 2 ≥ x ^ 2 / 2 - 9 * σ ^ 2 / 4 := by
    nlinarith [sq_nonneg (x - 3 * σ)]
  have h1 : ((x - 3 * σ / 2) / σ) ^ 2 ≥ x ^ 2 / (2 * σ ^ 2) - 9 / 4 := by
    rw [div_pow, ge_iff_le, le_div_iff₀ (by positivity)]
    have he : (x ^ 2 / (2 * σ ^ 2) - 9 / 4) * σ ^ 2 = x ^ 2 / 2 - 9 * σ ^ 2 / 4 := by
      field_simp
    rw [he]; exact h2
  rw [gmajor, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h3 : x ^ 2 / (2 * σ ^ 2) - ((x - 3 * σ / 2) / σ) ^ 2 ≤ 9 / 4 := by linarith [h1]
  have h4 : Real.pi * (x ^ 2 / (2 * σ ^ 2) - ((x - 3 * σ / 2) / σ) ^ 2) ≤ Real.pi * (9 / 4) :=
    mul_le_mul_of_nonneg_left h3 Real.pi_pos.le
  rw [div_eq_mul_inv] at h4 ⊢
  ring_nf at h4 ⊢
  linarith

/-- The Gaussian majorant `gmajor σ` is summable on `ℤ` for `σ ≥ 1`. -/
lemma summable_gmajor (σ : ℝ) (hσ : 1 ≤ σ) :
    Summable (fun s : ℤ => gmajor σ (s : ℝ)) := by
  have hσpos : 0 < σ := lt_of_lt_of_le zero_lt_one hσ
  have hd : 0 < Real.pi / (2 * σ ^ 2) := by positivity
  have hbase : Summable (fun s : ℤ => Real.exp (-(Real.pi / (2 * σ ^ 2)) * (s : ℝ) ^ 2)) :=
    summable_exp_neg_sq_int hd
  have hbase' : Summable (fun s : ℤ => Real.exp (-(Real.pi) * (s : ℝ) ^ 2 / (2 * σ ^ 2))) :=
    hbase.congr (fun s => by congr 1; ring)
  have hmaj : Summable (fun s : ℤ =>
      Real.exp (5 * Real.pi / 2) * Real.exp (-(Real.pi) * (s : ℝ) ^ 2 / (2 * σ ^ 2))) :=
    Summable.mul_left _ hbase'
  exact Summable.of_nonneg_of_le (fun s => gmajor_nonneg σ (s : ℝ))
    (fun s => gmajor_le_exp_neg hσpos (s : ℝ)) hmaj

/-! ## Summability of the majorant-weighted class sums -/

/-- For fixed `r`, `s ↦ gmajor (S:ℝ) (s:ℝ) * normSq (TZ D R S γ r s)` is summable. -/
lemma summable_majorant_TZ (D R S : ℕ) (hS : 1 ≤ S) (γ : ℕ → ℕ → ℂ) (r : ℕ) :
    Summable (fun s : ℤ => gmajor (S : ℝ) (s : ℝ) * Complex.normSq (TZ D R S γ r s)) := by
  have hg : Summable (fun s : ℤ => gmajor (S : ℝ) (s : ℝ)) :=
    summable_gmajor (S : ℝ) (by exact_mod_cast hS)
  have hC : Summable (fun s : ℤ =>
      (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, ‖γ a d‖) ^ 2 * gmajor (S : ℝ) (s : ℝ)) :=
    Summable.mul_left _ hg
  refine Summable.of_nonneg_of_le (fun s => ?_)
    (fun s => ?_) hC
  · exact mul_nonneg (gmajor_nonneg _ _) (Complex.normSq_nonneg _)
  · calc gmajor (S : ℝ) (s : ℝ) * Complex.normSq (TZ D R S γ r s)
        ≤ gmajor (S : ℝ) (s : ℝ)
            * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, ‖γ a d‖) ^ 2 :=
          mul_le_mul_of_nonneg_left (normSq_TZ_le D R S γ r s) (gmajor_nonneg _ _)
      _ = (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, ‖γ a d‖) ^ 2
            * gmajor (S : ℝ) (s : ℝ) := by ring

/-! ## The main estimate -/

theorem Wdyad_le_majorant (D R S : ℕ) (hS : 1 ≤ S) (γ : ℕ → ℕ → ℂ) :
    Wdyad D R S γ ≤
      ∑ r ∈ Finset.Ioc R (2 * R),
        ∑' s : ℤ, (gmajor (S:ℝ) (s:ℝ)) * Complex.normSq (TZ D R S γ r s) := by
  rw [Wdyad]
  have hinner : ∀ r : ℕ,
      (∑ s ∈ Finset.Ioc S (2 * S),
        Complex.normSq (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
          γ a d * Mentry d a r s))
        = ∑ s ∈ Finset.Ioc S (2 * S), Complex.normSq (TZ D R S γ r (s : ℤ)) := by
    intro r
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [TZ_ofNat]
  simp_rw [hinner]
  refine Finset.sum_le_sum (fun r _ => ?_)
  set K : Finset ℤ := (Finset.Ioc S (2 * S)).image (fun s : ℕ => (s : ℤ)) with hK
  have hKmem : ∀ z ∈ K, ∃ s ∈ Finset.Ioc S (2 * S), (s : ℤ) = z := by
    intro z hz
    rw [hK, Finset.mem_image] at hz
    obtain ⟨s, hs, hsz⟩ := hz
    exact ⟨s, hs, hsz⟩
  have hsum_image :
      ∑ z ∈ K, Complex.normSq (TZ D R S γ r z)
        = ∑ s ∈ Finset.Ioc S (2 * S), Complex.normSq (TZ D R S γ r (s : ℤ)) := by
    rw [hK, Finset.sum_image]
    intro a _ b _ h
    exact Nat.cast_injective h
  rw [← hsum_image]
  calc ∑ z ∈ K, Complex.normSq (TZ D R S γ r z)
      ≤ ∑ z ∈ K, gmajor (S : ℝ) (z : ℝ) * Complex.normSq (TZ D R S γ r z) := by
        refine Finset.sum_le_sum (fun z hz => ?_)
        obtain ⟨s, hs, hsz⟩ := hKmem z hz
        have hs1 : S ≤ s := (Finset.mem_Ioc.mp hs).1.le
        have hs2 : s ≤ 2 * S := (Finset.mem_Ioc.mp hs).2
        have hzr : (z : ℝ) = (s : ℝ) := by rw [← hsz]; push_cast; ring
        have hgm : 1 ≤ gmajor (S : ℝ) (z : ℝ) := by
          rw [hzr]
          refine gmajor_ge_one ?_ ?_ ?_
          · exact_mod_cast (lt_of_lt_of_le zero_lt_one hS)
          · exact_mod_cast hs1
          · exact_mod_cast hs2
        calc Complex.normSq (TZ D R S γ r z)
            = 1 * Complex.normSq (TZ D R S γ r z) := (one_mul _).symm
          _ ≤ gmajor (S : ℝ) (z : ℝ) * Complex.normSq (TZ D R S γ r z) :=
              mul_le_mul_of_nonneg_right hgm (Complex.normSq_nonneg _)
    _ ≤ ∑' z : ℤ, gmajor (S : ℝ) (z : ℝ) * Complex.normSq (TZ D R S γ r z) :=
        Summable.sum_le_tsum K (fun z _ => mul_nonneg (gmajor_nonneg _ _) (Complex.normSq_nonneg _))
          (summable_majorant_TZ D R S hS γ r)

end

end Work.FIArea4
