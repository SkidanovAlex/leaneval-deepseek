import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- **Hölder + boundedness gives Hölder with any smaller exponent.**

If `f` is `p`-Hölder with constant `A`, `g` is `q`-Hölder with constant `B`, and the combined
field `y ↦ f y + s • g y` is bounded by `M`, then that combined field is `c`-Hölder with
constant `max (A + |s| * B) (2 * M)` for every `0 < c ≤ min p q`.

For `‖a - b‖ ≤ 1` the two Hölder estimates are combined directly and `‖a-b‖^p, ‖a-b‖^q` are
dominated by `‖a-b‖^c`; for `‖a - b‖ ≥ 1` the uniform bound together with `‖a-b‖^c ≥ 1`
gives the claim. -/
theorem exists_holder_bound_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → E} {s A B p q c M : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hc : 0 < c) (hcp : c ≤ p) (hcq : c ≤ q)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hf : ∀ a b : E, ‖f a - f b‖ ≤ A * ‖a - b‖ ^ p)
    (hg : ∀ a b : E, ‖g a - g b‖ ≤ B * ‖a - b‖ ^ q)
    (hbd : ∀ y : E, ‖f y + s • g y‖ ≤ M) :
    ∀ a b : E, ‖(f a + s • g a) - (f b + s • g b)‖ ≤ max (A + |s| * B) (2 * M) * ‖a - b‖ ^ c := by
  have _ := hp
  have _ := hq
  intro a b
  have htc_nonneg : 0 ≤ ‖a - b‖ ^ c := Real.rpow_nonneg (norm_nonneg _) c
  rcases le_or_gt ‖a - b‖ 1 with ht1 | ht1
  · -- Small distances: combine the two Hölder bounds and lower the exponents to `c`.
    have htp : ‖a - b‖ ^ p ≤ ‖a - b‖ ^ c :=
      Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) ht1 hc.le hcp
    have htq : ‖a - b‖ ^ q ≤ ‖a - b‖ ^ c :=
      Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) ht1 hc.le hcq
    have hfp : ‖f a - f b‖ ≤ A * ‖a - b‖ ^ c :=
      le_trans (hf a b) (mul_le_mul_of_nonneg_left htp hA)
    have hgq : ‖g a - g b‖ ≤ B * ‖a - b‖ ^ c :=
      le_trans (hg a b) (mul_le_mul_of_nonneg_left htq hB)
    have hsg : ‖s • (g a - g b)‖ ≤ |s| * (B * ‖a - b‖ ^ c) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hgq (abs_nonneg s)
    have hsub : (f a + s • g a) - (f b + s • g b) = (f a - f b) + s • (g a - g b) := by
      rw [smul_sub]; abel
    calc ‖(f a + s • g a) - (f b + s • g b)‖
        = ‖(f a - f b) + s • (g a - g b)‖ := by rw [hsub]
      _ ≤ ‖f a - f b‖ + ‖s • (g a - g b)‖ := norm_add_le _ _
      _ ≤ A * ‖a - b‖ ^ c + |s| * (B * ‖a - b‖ ^ c) := add_le_add hfp hsg
      _ = (A + |s| * B) * ‖a - b‖ ^ c := by ring
      _ ≤ max (A + |s| * B) (2 * M) * ‖a - b‖ ^ c :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) htc_nonneg
  · -- Large distances: use the uniform bound and `‖a - b‖^c ≥ 1`.
    have h1 : 1 ≤ ‖a - b‖ := le_of_lt ht1
    have hM2 : ‖(f a + s • g a) - (f b + s • g b)‖ ≤ 2 * M := by
      calc ‖(f a + s • g a) - (f b + s • g b)‖
          ≤ ‖f a + s • g a‖ + ‖f b + s • g b‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (hbd a) (hbd b)
        _ = 2 * M := by ring
    have htc : 1 ≤ ‖a - b‖ ^ c := Real.one_le_rpow h1 hc.le
    calc ‖(f a + s • g a) - (f b + s • g b)‖
        ≤ 2 * M := hM2
      _ = 2 * M * 1 := (mul_one _).symm
      _ ≤ 2 * M * ‖a - b‖ ^ c := mul_le_mul_of_nonneg_left htc (by linarith)
      _ ≤ max (A + |s| * B) (2 * M) * ‖a - b‖ ^ c :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) htc_nonneg

end Work.CoreResiduals.BiotSavart
