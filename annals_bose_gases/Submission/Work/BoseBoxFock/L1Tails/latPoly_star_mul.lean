import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.L1Tails.latDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- The plane waves satisfy `conj (latWave v x) * latWave w x = latWave (w - v) x`:
the exponents `-I⟪v,x⟫` and `I⟪w,x⟫` add to `I⟪w−v,x⟫`. -/
lemma star_latWave_mul (v w x : E3) :
    (starRingEnd ℂ) (latWave v x) * latWave w x = latWave (w - v) x := by
  simp only [latWave]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal, inner_sub_left]
  push_cast
  ring

/-- The lattice momentum is additive in the index: `kappaL ℓ m - kappaL ℓ n = kappaL ℓ (m - n)`
(`kappaL ℓ n = ℓ⁻¹ • vec n` and `vec` is additive, `Work.BoseB4.vec_sub`). -/
lemma kappaL_sub (ℓ : ℝ) (m n : Fin 3 → ℤ) :
    kappaL ℓ m - kappaL ℓ n = kappaL ℓ (m - n) := by
  rw [kappaL_eq, kappaL_eq, kappaL_eq, ← smul_sub, Work.BoseB4.vec_sub]
  rfl

/-- The pointwise expansion of the modulus square of the lattice trigonometric polynomial
`latPoly ℓ S c x = ∑ n ∈ S, c n * latWave (kappaL ℓ n) x` into the double sum over the difference
momenta:

`(conj P) * P = ∑ n ∈ S, ∑ m ∈ S, conj (c n) * c m * latWave (kappaL ℓ (m - n)) x`.

Its real part is `‖latPoly ℓ S c x‖²` (since `conj z * z = ↑‖z‖²`); integrating the right-hand side
against the PROVED box-wave orthogonality `boxWaveIntegralScaled` gives the Parseval identity.

Proof hints: `latPoly`, `latWave` unfold to finite sums of `c n * exp (I * ⟪kappaL ℓ n, x⟫)`
(`Work.BoseBoxFock.L1Tails.latPoly`, `Work.BoseBoxFock.L1Tails.latWave`); use `map_sum`, `map_mul`,
`Finset.sum_mul_sum`, `Complex.exp_conj`, `Complex.exp_add`, `map_sub`, `inner_sub_left`,
`inner_add_right`, `Work.BoseBoxFock.L1Tails.kappaL_eq`, and the PROVED `Work.BoseB4.vec_sub`
(`vec m - vec n = vec (fun i => m i - n i)`) to identify the exponent of
`conj (latWave (kappaL ℓ n) x) * latWave (kappaL ℓ m) x` with `I * ⟪kappaL ℓ (m - n), x⟫`. -/
theorem latPoly_star_mul {ℓ : ℝ} (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → ℂ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    (starRingEnd ℂ) (Work.BoseBoxFock.L1Tails.latPoly ℓ S c x)
        * Work.BoseBoxFock.L1Tails.latPoly ℓ S c x
      = ∑ n ∈ S, ∑ m ∈ S, (starRingEnd ℂ) (c n) * c m
          * Work.BoseBoxFock.L1Tails.latWave (Work.BoseBoxFock.kappaL ℓ (m - n)) x := by
  have hP : latPoly ℓ S c x = ∑ n ∈ S, c n * latWave (kappaL ℓ n) x := rfl
  rw [hP, map_sum]
  simp only [map_mul]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  rw [show (starRingEnd ℂ) (c n) * (starRingEnd ℂ) (latWave (kappaL ℓ n) x)
        * (c m * latWave (kappaL ℓ m) x)
      = (starRingEnd ℂ) (c n) * c m
        * ((starRingEnd ℂ) (latWave (kappaL ℓ n) x) * latWave (kappaL ℓ m) x) from by ring]
  rw [star_latWave_mul, kappaL_sub]

end Work.BoseBoxFock.L1Tails
