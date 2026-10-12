import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.integral_translate_kinFT_phase
import Submission.Work.BoseBoxFock.summable_kinFT_lattice_phase
import Submission.Work.BoseFixR.poisson_scaled
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.latticePoisson_kernel` — the lattice Poisson (aliasing) identity

For `ℓ > 0`, `W : ℝ³ → ℂ` smooth with compact support and every `z ∈ ℝ³`,

    ∑'_n  Ŵ(k_n) · e^{i⟪k_n,z⟫}  =  ℓ³ · ∑'_m W (z + ℓ·m),

where `k_n = kmomInt ℓ n = (2π/ℓ) · latVec n` is the sampling lattice `(2π/ℓ)ℤ³` and
`Ŵ(p) = Submission.BoseGases.kinFT W p = ∫_y e^{−i⟪p,y⟫}W(y)dy` is the `p`-convention Fourier
transform.  Equivalently: sampling the Fourier transform of `W` on the lattice `(2π/ℓ)ℤ³` and
recombining with the phase `e^{i⟪k_n,z⟫}` is the same as periodizing `W` on the dual lattice
`ℓℤ³`.

## Proof

The identity is the corpus's Poisson summation `Work.BoseFixR.poisson_scaled` for the lattice
`ℓℤ³`, applied to the translated function `F = W(· + z)`:

    ∑'_m ∫_x F(x)·e^{−i⟪ℓ⁻¹•vec m, x⟫}dx = ℓ³ ∑'_d F(lat ℓ d).

The two translations are:

* *Fourier covariance of a translation* — `kinFT (W(· + z)) p = e^{i⟪p,z⟫}·kinFT W p`, i.e.
  `∫_x W(x+z)e^{−i⟪p,x⟫}dx = Ŵ(p)·e^{i⟪p,z⟫}` (`Work.BoseBoxFock.integral_translate_kinFT_phase`,
  proved from `Work.BSKinetic.Decomp.kinFT_comp_add`), which turns the target's summand
  `Ŵ(k_n)e^{i⟪k_n,z⟫}` into the Poisson integrand `∫_x F(x)e^{−i⟪k_n,x⟫}dx`;
* *the dual lattices* — `lat ℓ d = ℓ • latVec d`.

The summability hypothesis demanded by `poisson_scaled` is supplied by
`Work.BoseBoxFock.summable_kinFT_lattice_phase` (polynomial decay of the Fourier transform of
the smooth compactly supported `W`: `Work.OneBodyKin.kinFT_decay_le` +
`Work.BoseBoxFock.summable_one_add_norm_latVec_pow_inv`); the phase factor has modulus `1` and
is irrelevant to convergence.
-/

noncomputable section

open MeasureTheory

open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The Poisson dual lattice of the corpus theorem is `ℓ • latVec n`: `lat ℓ n = ℓ • latVec n`. -/
private lemma lat_eq_smul_latVec (ℓ : ℝ) (n : Fin 3 → ℤ) :
    Work.BoseFixR.lat ℓ n = ℓ • latVec n := by
  ext i
  simp [Work.BoseFixR.lat, latVec]

/-! ## The target -/

theorem latticePoisson_kernel (ℓ : ℝ) (hℓ : 0 < ℓ) (W : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) (hWs : HasCompactSupport W) (z : EuclideanSpace ℝ (Fin 3)) :
    (∑' n : Fin 3 → ℤ, Submission.BoseGases.kinFT W (Work.BoseBoxFock.kmomInt ℓ n)
        * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) z : ℂ)))
      = (ℓ : ℂ) ^ 3 * (∑' m : Fin 3 → ℤ,
          W (z + ℓ • WithLp.toLp 2 (fun i : Fin 3 => (m i : ℝ)))) := by
  classical
  -- the translated function whose Fourier samples are the target's summands
  set F : E3 → ℂ := fun x => W (x + z) with hF
  have hFc : Continuous F :=
    hW.continuous.comp (continuous_id.add continuous_const)
  have hFs : HasCompactSupport F :=
    hWs.comp_homeomorph (Homeomorph.addRight z)
  -- **the term identity**: the target's summand is exactly the Poisson integrand
  have hterm : ∀ n : Fin 3 → ℤ,
      (∫ x : E3, F x * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) x : ℂ))))
        = Submission.BoseGases.kinFT W (kmomInt ℓ n)
          * Complex.exp (Complex.I * (inner ℝ (kmomInt ℓ n) z : ℂ)) := by
    intro n
    simpa only [hF] using integral_translate_kinFT_phase (W := W) z (kmomInt ℓ n)
  -- **the summability input** of `poisson_scaled`: decay of `kinFT W` on the sampling lattice
  have hsummKin : Summable (fun n : Fin 3 → ℤ =>
      Submission.BoseGases.kinFT W (kmomInt ℓ n)
        * Complex.exp (Complex.I * (inner ℝ (kmomInt ℓ n) z : ℂ))) :=
    summable_kinFT_lattice_phase (ℓ := ℓ) hℓ hW hWs z
  have hsum : Summable (fun m : Fin 3 → ℤ =>
      ∫ x : E3, F x * Complex.exp (-(Complex.I * (inner ℝ (ℓ⁻¹ • Work.BoseB4.vec m) x : ℂ)))) :=
    hsummKin.congr (fun m => (hterm m).symm)
  -- **Poisson summation** for `F` on the lattice `ℓℤ³`
  have hpois := Work.BoseFixR.poisson_scaled (ℓ := ℓ) hℓ hFc hFs hsum
  calc (∑' n : Fin 3 → ℤ, Submission.BoseGases.kinFT W (kmomInt ℓ n)
        * Complex.exp (Complex.I * (inner ℝ (kmomInt ℓ n) z : ℂ)))
      = ∑' n : Fin 3 → ℤ,
          ∫ x : E3, F x * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) x : ℂ))) :=
        tsum_congr (fun n => (hterm n).symm)
    _ = (ℓ : ℂ) ^ 3 * ∑' d : Fin 3 → ℤ, F (Work.BoseFixR.lat ℓ d) := hpois
    _ = (ℓ : ℂ) ^ 3 * (∑' m : Fin 3 → ℤ,
          W (z + ℓ • WithLp.toLp 2 (fun i : Fin 3 => (m i : ℝ)))) := by
        congr 1
        refine tsum_congr (fun m => ?_)
        rw [hF]
        show W (Work.BoseFixR.lat ℓ m + z) = W (z + ℓ • latVec m)
        rw [lat_eq_smul_latVec]
        exact congrArg W (add_comm _ _)

end Work.BoseBoxFock
