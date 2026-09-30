import Mathlib
import Submission.Work.BW.Est17Ext
import Submission.Work.BW.DefsAC
import Submission.Work.BW.prod_formula_log
import Submission.Work.BW.est17_finrank
import Submission.Work.BW.est15_kummer_sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open NumberField

/-- **The `2`-adic (finite-place) sum.** With the Kummer hypotheses
(`η_j ≠ 0`, `ρ_j ^ 2 = φ (η_j)`, `KummerCond η`) the field `L = EL φ ρ` has
`[L : ℚ] = 2^r · [K : ℚ]` (`est17_finrank`), and `inclE φ ρ (2 : K) = (2 : L)`.  For every infinite
place `v` of a number field, `v (2 : L) = 2` (`NumberField.InfinitePlace.map_natCast`), so the
product formula `prod_formula_log` for `2 ≠ 0` gives
`(Σ_v v.mult · log 2) + Σᶠ_w log (w 2) = 0`; for a finite place `w`, `w (2) ≤ 1` because `2` is
integral (`FinitePlace.mk_apply` with `FinitePlace.norm_le_one`), so every logarithm is `≤ 0` and
`Σᶠ_w |log (w 2)| = (Σ_v v.mult) · log 2 = [L:ℚ] · log 2 = 2^r · [K:ℚ] · log 2`
(`NumberField.InfinitePlace.sum_mult_eq`).  (Closely parallel to the already-proved
`Work.BW.est15_kummer_sum`, which is the `r = 0` / no-Kummer case for an arbitrary number field.) -/
theorem est17_finsum_log_two {K : Type*} [Field K] [NumberField K] {r : ℕ} {φ : K →+* ℂ}
    {ρ : Fin r → ℂ} {η : Fin r → K} (hη : ∀ j, η j ≠ 0) (hρ : ∀ j, ρ j ^ 2 = φ (η j))
    (hK : KummerCond η) [inst : NumberField (EL φ ρ)] :
    (∑ᶠ w : NumberField.FinitePlace (EL φ ρ), |Real.log (w (inclE φ ρ (2 : K)))|)
      = (2 : ℝ) ^ r * (dK K : ℝ) * Real.log 2 := by
  -- `inclE φ ρ (2 : K)` is the natural number `2` of `L = EL φ ρ`.
  have hx2 : inclE φ ρ (2 : K) = (2 : EL φ ρ) := by
    ext
    simp only [inclE_coe]
    exact map_ofNat φ 2
  have hxne : inclE φ ρ (2 : K) ≠ 0 := by rw [hx2]; norm_num
  -- The logarithmic product formula for `2 ∈ L`.
  have hpf := prod_formula_log (K := EL φ ρ) (x := inclE φ ρ (2 : K)) hxne
  -- At an infinite place of `L`, the element `2` has absolute value `2`.
  have h2c : (2 : EL φ ρ) = ((2 : ℕ) : EL φ ρ) := by norm_num
  have hinf : ∀ v : NumberField.InfinitePlace (EL φ ρ),
      v (inclE φ ρ (2 : K)) = (2 : ℝ) := by
    intro v
    rw [hx2, h2c, NumberField.InfinitePlace.map_natCast]
    norm_num
  -- The archimedean part is `[L : ℚ] · log 2`.
  have hsum_inf : (∑ v : NumberField.InfinitePlace (EL φ ρ),
        ((v.mult : ℕ) : ℝ) * Real.log (v (inclE φ ρ (2 : K))))
      = (Module.finrank ℚ (EL φ ρ) : ℝ) * Real.log 2 := by
    simp only [hinf]
    rw [← Finset.sum_mul]
    congr 1
    have hsum := NumberField.InfinitePlace.sum_mult_eq (K := EL φ ρ)
    rw [← hsum]
    push_cast
    rfl
  rw [hsum_inf] at hpf
  -- Hence the finite-place sum of the logarithms is `-[L : ℚ] · log 2`.
  have hfin : (∑ᶠ w : NumberField.FinitePlace (EL φ ρ),
        Real.log (w (inclE φ ρ (2 : K)))) = -((Module.finrank ℚ (EL φ ρ) : ℝ) * Real.log 2) := by
    linarith
  -- Every finite-place logarithm is `≤ 0`, since `2` is integral.
  have hle : ∀ w : NumberField.FinitePlace (EL φ ρ),
      Real.log (w (inclE φ ρ (2 : K))) ≤ 0 := by
    intro w
    refine Real.log_nonpos (apply_nonneg w _) ?_
    rw [hx2]
    have hv : IsNonarchimedean (fun x : EL φ ρ => w x) := FinitePlace.add_le w
    exact hv.apply_natCast_le_one (map_zero_le w 1) (map_one w)
  -- So the absolute values may be replaced by `-log`.
  have hcongr : (∑ᶠ w : NumberField.FinitePlace (EL φ ρ),
        |Real.log (w (inclE φ ρ (2 : K)))|)
      = ∑ᶠ w : NumberField.FinitePlace (EL φ ρ), -Real.log (w (inclE φ ρ (2 : K))) := by
    refine finsum_congr (fun w => ?_)
    rw [abs_of_nonpos (hle w)]
  rw [hcongr, finsum_neg_distrib, hfin]
  -- Finally `[L : ℚ] = 2^r · [K : ℚ]`.
  have hfr : (Module.finrank ℚ (EL φ ρ) : ℝ) = (2 : ℝ) ^ r * (dK K : ℝ) := by
    rw [est17_finrank hη hρ hK]
    push_cast
    ring
  rw [hfr]
  ring

end Work.BW
