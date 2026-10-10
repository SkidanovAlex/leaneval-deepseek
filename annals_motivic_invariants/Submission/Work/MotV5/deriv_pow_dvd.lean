import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

/-- If `R` is a discrete valuation ring with irreducible `p`, `g` has additive valuation `m ≥ 1`,
and a derivation `D : A → K` maps the image of `R` into itself, then `D (algebraMap R K g)` is
divisible by `p ^ (m - 1)` with quotient again in the image of `R`. -/
theorem deriv_pow_dvd {A R K : Type*} [CommRing A] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra A K] [Algebra R K]
    (D : Derivation A K K)
    (hD : ∀ x : R, ∃ y : R, D (algebraMap R K x) = algebraMap R K y)
    {p : R} (hp : Irreducible p) {m : ℕ} (hm : 1 ≤ m) {g : R}
    (hg : IsDiscreteValuationRing.addVal R g = (m : ℕ∞)) :
    ∃ z : R, D (algebraMap R K g) = algebraMap R K p ^ (m - 1) * algebraMap R K z := by
  -- `p` is a uniformizer, so `addVal p^m = m = addVal g`, i.e. `p^m ∣ g`.
  obtain ⟨c, hc⟩ : p ^ m ∣ g := by
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd]
    rw [hp.addVal_pow, hg]
  -- `D` maps the image of `R` into itself.
  obtain ⟨w, hw⟩ := hD c
  obtain ⟨y, hy⟩ := hD p
  refine ⟨p * w + (m : R) * c * y, ?_⟩
  have hpow : (algebraMap R K p) ^ m = (algebraMap R K p) ^ (m - 1) * algebraMap R K p := by
    conv_lhs => rw [← Nat.sub_add_cancel hm]
    rw [pow_succ]
  rw [hc, map_mul, map_pow]
  rw [Derivation.leibniz, hw, Derivation.leibniz_pow, hy]
  simp only [smul_eq_mul, nsmul_eq_mul]
  simp only [map_add, map_mul, map_natCast]
  rw [hpow]
  first | refl_ring1 | ring

end Work.MotV5
