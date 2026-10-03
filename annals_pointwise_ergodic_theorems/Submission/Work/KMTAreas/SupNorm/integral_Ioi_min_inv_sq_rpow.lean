import Mathlib

namespace Work.KMTAreas.SupNorm

/-!
# The integral of `min A (B / x²) ^ q` over `(0, ∞)`

For `A, B > 0` and `q > 1/2` we compute

`∫_{0}^{∞} (min A (B / x²))^q dx = A^q · √(B/A) + B^q · (√(B/A))^{1-2q} / (2q-1)`.

The integrand equals the constant `A^q` on `(0, c]` and `B^q x^{-2q}` on `(c, ∞)`, where
`c = √(B/A)` is the crossing point at which `B/x²` becomes smaller than `A`.  Splitting the
integral at `c` and using `∫_c^∞ x^{-2q} dx = c^{1-2q}/(2q-1)` (valid since `-2q < -1`) gives
the claim.
-/

open MeasureTheory Real

theorem integral_Ioi_min_inv_sq_rpow {A B q : ℝ} (hA : 0 < A) (hB : 0 < B) (hq : 1 / 2 < q) :
    ∫ x in Set.Ioi (0 : ℝ), (min A (B / x ^ 2)) ^ q
      = A ^ q * Real.sqrt (B / A)
        + B ^ q * (Real.sqrt (B / A)) ^ (1 - 2 * q) / (2 * q - 1) := by
  -- The crossing point `c = √(B/A)`.
  set c : ℝ := Real.sqrt (B / A) with hcdef
  have hAB : 0 < B / A := div_pos hB hA
  have hcpos : 0 < c := by rw [hcdef]; exact Real.sqrt_pos.2 hAB
  have hc2 : c ^ 2 = B / A := by rw [hcdef]; exact Real.sq_sqrt hAB.le
  have hden1 : (1 - 2 * q) ≠ 0 := by linarith
  have hden2 : (2 * q - 1) ≠ 0 := by linarith
  have hneg : -2 * q < -1 := by linarith
  -- On `(0, c]` the minimum is `A`; on `(c, ∞)` it is `B / x²`.
  have hmin1 : ∀ x ∈ Set.Ioc (0 : ℝ) c, min A (B / x ^ 2) = A := by
    intro x hx
    obtain ⟨hx0, hxc⟩ := hx
    apply min_eq_left
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < x ^ 2)]
    calc A * x ^ 2 ≤ A * c ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hA.le
          exact pow_le_pow_left₀ hx0.le hxc 2
      _ = B := by rw [hc2, mul_div_cancel₀ B hA.ne']
  have hmin2 : ∀ x ∈ Set.Ioi c, min A (B / x ^ 2) = B / x ^ 2 := by
    intro x hx
    have hxpos : 0 < x := hcpos.trans hx
    apply min_eq_right
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < x ^ 2)]
    calc B = A * c ^ 2 := by rw [hc2, mul_div_cancel₀ B hA.ne']
      _ ≤ A * x ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hA.le
          exact (pow_lt_pow_left₀ hx hcpos.le (by norm_num : (2 : ℕ) ≠ 0)).le
  -- Rewriting the `q`-th power.
  have hdiv : ∀ x, 0 < x → (B / x ^ 2) ^ q = B ^ q * x ^ (-2 * q) := by
    intro x hx
    rw [Real.div_rpow hB.le (by positivity : (0 : ℝ) ≤ x ^ 2)]
    rw [← Real.rpow_two x]
    rw [← Real.rpow_mul hx.le (2 : ℝ) q]
    rw [div_eq_mul_inv, ← Real.rpow_neg hx.le ((2 : ℝ) * q)]
    congr 1
    ring_nf
  -- Integrability on the two pieces.
  have hint1 : IntegrableOn (fun x : ℝ => (min A (B / x ^ 2)) ^ q) (Set.Ioc (0 : ℝ) c) volume := by
    refine IntegrableOn.congr_fun (f := fun _ : ℝ => A ^ q) ?_ ?_ measurableSet_Ioc
    · exact integrableOn_const (by rw [Real.volume_Ioc]; simp)
    · intro x hx
      change A ^ q = (min A (B / x ^ 2)) ^ q
      rw [hmin1 x hx]
  have hint2 : IntegrableOn (fun x : ℝ => (min A (B / x ^ 2)) ^ q) (Set.Ioi c) volume := by
    refine IntegrableOn.congr_fun (f := fun x : ℝ => B ^ q * x ^ (-2 * q)) ?_ ?_ measurableSet_Ioi
    · exact (integrableOn_Ioi_rpow_of_lt hneg hcpos).const_mul (B ^ q)
    · intro x hx
      change B ^ q * x ^ (-2 * q) = (min A (B / x ^ 2)) ^ q
      rw [hmin2 x hx, hdiv x (hcpos.trans hx)]
  -- `(0, ∞) = (0, c] ∪ (c, ∞)`.
  have hunion : Set.Ioc (0 : ℝ) c ∪ Set.Ioi c = Set.Ioi (0 : ℝ) := by
    ext x
    constructor
    · rintro (⟨h1, h2⟩ | h3)
      · exact h1
      · exact hcpos.trans h3
    · intro hx
      by_cases h : x ≤ c
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (lt_of_not_ge h)
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) c) (Set.Ioi c) := Set.Ioc_disjoint_Ioi le_rfl
  rw [← hunion, setIntegral_union hdisj measurableSet_Ioi hint1 hint2]
  -- The two integrals.
  have e1 : ∫ x in Set.Ioc (0 : ℝ) c, (min A (B / x ^ 2)) ^ q = A ^ q * c := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun x hx => by rw [hmin1 x hx])]
    rw [setIntegral_const, Real.volume_real_Ioc_of_le hcpos.le, smul_eq_mul]
    ring
  have e2 : ∫ x in Set.Ioi c, (min A (B / x ^ 2)) ^ q
      = B ^ q * c ^ (1 - 2 * q) / (2 * q - 1) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun x hx => by rw [hmin2 x hx, hdiv x (hcpos.trans hx)])]
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hneg hcpos]
    rw [show -2 * q + 1 = 1 - 2 * q by ring]
    field_simp
    ring
  rw [e1, e2]

end Work.KMTAreas.SupNorm
