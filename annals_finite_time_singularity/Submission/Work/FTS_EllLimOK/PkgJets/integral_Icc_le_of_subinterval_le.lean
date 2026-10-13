import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Exhaustion of an interval by shrinking subintervals.**

If `g` is integrable on the open interval `(a,b)` and every interval integral
`∫_x^y g` over a subinterval `(x,y) ⊆ (a,b)` is at most `K`, then the integral
over `[a,b]` is at most `K`.

The proof exhausts `(a,b)` by the increasing family of intervals
`(a + c n, b - c n)` with `c n = (b-a)/(4(n+1)) ↓ 0` and applies monotone
convergence of the set integrals (`MeasureTheory.tendsto_setIntegral_of_monotone`).
Nonnegativity of `g` is *not* needed: integrability on `(a,b)` alone is enough
for the exhausting integrals to converge to the integral over `(a,b)` (the
dominating function `‖g‖` is integrable). -/
theorem integral_Icc_le_of_subinterval_le {g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hint : IntegrableOn g (Set.Ioo a b))
    (hnn : ∀ x ∈ Set.Ioo a b, 0 ≤ g x) {K : ℝ}
    (hK : ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, x < y → (∫ t in x..y, g t) ≤ K) :
    (∫ t in Set.Icc a b, g t) ≤ K := by
  have hba : 0 < b - a := sub_pos.mpr hab
  -- `hnn` is not needed for this upper bound, but it is consistent with the conclusion
  -- (`g ≥ 0` on `(a,b)` and `∫_a^b g ≤ K`); we keep the reference for documentation.
  have _hnn := hnn
  -- the shrinking half-width `c n = (b-a)/(4(n+1))`
  set c : ℕ → ℝ := fun n => (b - a) * (4 * ((n : ℝ) + 1))⁻¹ with hc
  have hc_eq : ∀ n, c n = (b - a) * (4 * ((n : ℝ) + 1))⁻¹ := fun n => rfl
  have hcpos : ∀ n, 0 < c n := by
    intro n
    rw [hc_eq n]
    exact mul_pos hba (inv_pos.mpr (by positivity))
  have hcnn : ∀ n, 0 ≤ c n := fun n => (hcpos n).le
  have hcle : ∀ n, c n ≤ (b - a) / 4 := by
    intro n
    rw [hc_eq n, div_eq_mul_inv]
    have h4 : (0:ℝ) < 4 := by norm_num
    have hle : (4:ℝ) ≤ 4 * ((n:ℝ) + 1) := by
      have h1 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    exact mul_le_mul_of_nonneg_left (inv_anti₀ h4 hle) hba.le
  have hxy : ∀ n, a + c n < b - c n := by
    intro n
    have h := hcle n
    linarith
  have hmeas : ∀ n, MeasurableSet (Set.Ioo (a + c n) (b - c n)) := fun _ => measurableSet_Ioo
  have hmono : Monotone (fun n : ℕ => Set.Ioo (a + c n) (b - c n)) := by
    intro m n hmn
    have hcnm : c n ≤ c m := by
      rw [hc_eq n, hc_eq m]
      have hmn' : (m:ℝ) + 1 ≤ (n:ℝ) + 1 := by
        have : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
        linarith
      have hpos : (0:ℝ) < 4 * ((m:ℝ)+1) := by positivity
      have hle : 4 * ((m:ℝ)+1) ≤ 4 * ((n:ℝ)+1) := by linarith
      exact mul_le_mul_of_nonneg_left (inv_anti₀ hpos hle) hba.le
    intro x hx
    rw [Set.mem_Ioo] at hx ⊢
    exact ⟨lt_of_le_of_lt (by linarith) hx.1, lt_of_lt_of_le hx.2 (by linarith)⟩
  -- the shrinking intervals exhaust `(a,b)`
  have hunion : (⋃ n, Set.Ioo (a + c n) (b - c n)) = Set.Ioo a b := by
    ext x
    constructor
    · rintro hxn
      rw [Set.mem_iUnion] at hxn
      obtain ⟨n, hxn⟩ := hxn
      rw [Set.mem_Ioo] at hxn ⊢
      exact ⟨lt_of_lt_of_le (lt_add_of_pos_right a (hcpos n)) hxn.1.le,
             lt_of_lt_of_le hxn.2 (sub_le_self b (hcnn n))⟩
    · rintro ⟨hx1, hx2⟩
      have hmin : 0 < min (x - a) (b - x) := lt_min (sub_pos.mpr hx1) (sub_pos.mpr hx2)
      obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / (4 * min (x - a) (b - x)))
      have hden : (0:ℝ) < 4 * ((n:ℝ) + 1) := by positivity
      have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have hcn : c n < min (x - a) (b - x) := by
        rw [hc_eq n, ← div_eq_mul_inv, div_lt_iff₀ hden]
        have h4δ : (0:ℝ) < 4 * min (x - a) (b - x) := by positivity
        rw [div_lt_iff₀ h4δ] at hn
        nlinarith [hn, h4δ, hn0]
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      exact ⟨by linarith [min_le_left (x-a) (b-x), hcn],
             by linarith [min_le_right (x-a) (b-x), hcn]⟩
  have hfi : IntegrableOn g (⋃ n, Set.Ioo (a + c n) (b - c n)) := by
    rw [hunion]; exact hint
  -- monotone convergence of the set integrals
  have htend := tendsto_setIntegral_of_monotone hmeas hmono hfi
  rw [hunion] at htend
  have hle : (∫ t in Set.Ioo a b, g t) ≤ K := by
    refine le_of_tendsto htend (Filter.Eventually.of_forall fun n => ?_)
    have hxmem : a + c n ∈ Set.Ioo a b :=
      ⟨lt_add_of_pos_right a (hcpos n), lt_of_lt_of_le (hxy n) (sub_le_self b (hcnn n))⟩
    have hymem : b - c n ∈ Set.Ioo a b :=
      ⟨lt_trans (lt_add_of_pos_right a (hcpos n)) (hxy n), sub_lt_self b (hcpos n)⟩
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (le_of_lt (hxy n))]
    exact hK (a + c n) hxmem (b - c n) hymem (hxy n)
  rw [integral_Icc_eq_integral_Ioo]
  exact hle

end Work.FTS_EllLimOK.PkgJets
