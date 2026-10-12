import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.Theta` — the theta/heat-kernel representation of the `ℤ³` lattice
Green's function

This module starts the missing chapter identified by `FINDING_farLatRow_sharp.md`: the
3-dimensional simple-cubic lattice Coulomb Green's function *with a neutralising background*.
The defining Fourier series
`Σ_{k∈ℤ³∖0} cos(2πk·u)/(4π²‖k‖²)` is only *conditionally* convergent, so (following the
operator's plan) the Green's function is **defined** through its absolutely convergent
heat-kernel (theta) representation

`G(u) = ∫_0^∞ ( (Σ_{n∈ℤ³} p_t(u − n)) − 1 ) dt`,   `p_t(x) = (4πt)^{−3/2} exp(−‖x‖²/(4t))`,

whose smooth part `h(u) = G(u) − 1/(4π‖u‖)` is the object that the far-leg lattice row needs:

`h(u) ≤ 1/(2π‖u‖)`  (numerically the sharp truth is `h ≤ 0`; the factor `3` of
`Work.BoseFixR.farLatRow` only needs `h ≤ 1/(2π‖u‖)` — see `FINDING_farLatRow_sharp.md` §4).

The *identification* of this object with the Fourier series (the Poisson-summation step) and
the Madelung evaluation of `h` are separate (delegated) lemmas; here we only set up the
definition, its basic structural properties, and the two easy analytic facts.

## Conventions

`p_t` is the heat kernel of `∂_t = Δ` on `ℝ³` (so `∫_{ℝ³} p_t = 1`), `Σ_n p_t(u − n)` is the
periodisation (the heat kernel on the unit torus `ℝ³/ℤ³`), and the `− 1` subtracts its mean
(`⨍_{cell} Σ_n p_t(· − n) = 1`), making the integrand the mean-zero part — exactly the
`(−Δ_♯)^{−1}` of the periodic Laplacian.
-/

noncomputable section

open scoped Real BigOperators
open MeasureTheory Set

namespace Work.BoseFixR.LatGreen

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The lattice point of `n : ℤ³`. -/
noncomputable def latVec (n : Fin 3 → ℤ) : ℝ³ := WithLp.toLp 2 (fun i => (n i : ℝ))

@[simp] lemma latVec_apply (n : Fin 3 → ℤ) (i : Fin 3) : latVec n i = (n i : ℝ) := rfl

lemma latVec_neg (n : Fin 3 → ℤ) : latVec (-n) = -latVec n := by
  ext i; simp [latVec]

lemma latVec_add (n m : Fin 3 → ℤ) : latVec (n + m) = latVec n + latVec m := by
  ext i; simp [latVec]

lemma latVec_sub (n m : Fin 3 → ℤ) : latVec (n - m) = latVec n - latVec m := by
  ext i; simp [latVec]

/-- The heat kernel of `∂_t = Δ` on `ℝ³`. -/
noncomputable def heatK3 (t : ℝ) (x : ℝ³) : ℝ :=
  (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-‖x‖ ^ 2 / (4 * t))

/-- The periodisation of the heat kernel (`= ` the heat kernel of the unit torus `ℝ³/ℤ³`). -/
noncomputable def heatPeriod (t : ℝ) (u : ℝ³) : ℝ :=
  ∑' n : Fin 3 → ℤ, heatK3 t (u - latVec n)

/-- **The periodisation is `ℤ³`-periodic.**  (This is why the pointwise lattice-Green's-function
bound may be assumed on the fundamental domain `[-1/2,1/2]³` only: the kernel on the torus is the
restriction of the periodic function.) -/
theorem heatPeriod_add_latVec (t : ℝ) (u : ℝ³) (m : Fin 3 → ℤ) :
    heatPeriod t (u + latVec m) = heatPeriod t u := by
  have hf : ∀ n : Fin 3 → ℤ, u + latVec m - latVec n = u - latVec (n - m) := by
    intro n
    rw [latVec_sub]
    abel
  rw [heatPeriod, heatPeriod]
  refine (tsum_congr (fun n => by rw [hf n])).trans ?_
  exact Equiv.tsum_eq (Equiv.addRight (-m)) (fun j : Fin 3 → ℤ => heatK3 t (u - latVec j))

/-- **The lattice Green's function `G` of `ℤ³` with a neutralising background**, through its
theta/heat-kernel representation.  (`G(u) = Σ_{k≠0}cos(2πk·u)/(4π²‖k‖²)` as a distribution.) -/
noncomputable def latGreen (u : ℝ³) : ℝ :=
  ∫ t in Ioi (0 : ℝ), (heatPeriod t u - 1)

/-- The same, in the form `u ↦ u + latVec m` inside the argument. -/
theorem latGreen_periodic (u : ℝ³) (m : Fin 3 → ℤ) :
    latGreen (u + latVec m) = latGreen u := by
  unfold latGreen
  exact integral_congr_ae (Filter.Eventually.of_forall fun t => by
    simp only [heatPeriod_add_latVec])

/-- **The smooth part `h`** of the lattice Green's function: `h(u) = G(u) − 1/(4π‖u‖)`.
This is the object of the far-leg crux `h(u) ≤ 1/(2π‖u‖)`. -/
noncomputable def latGreenSmooth (u : ℝ³) : ℝ :=
  latGreen u - 1 / (4 * Real.pi * ‖u‖)

lemma heatK3_nonneg {t : ℝ} (ht : 0 < t) (x : ℝ³) : 0 ≤ heatK3 t x := by
  unfold heatK3
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _)

lemma heatK3_pos {t : ℝ} (ht : 0 < t) (x : ℝ³) : 0 < heatK3 t x := by
  unfold heatK3
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

/-- `p_t` has total mass `1`. -/
theorem integral_heatK3 {t : ℝ} (ht : 0 < t) : ∫ x : ℝ³, heatK3 t x = 1 := by
  have hb : (0 : ℝ) < 1 / (4 * t) := by positivity
  have hfr : Module.finrank ℝ ℝ³ = 3 := by simp
  have hgauss : ∫ x : ℝ³, Real.exp (-(1 / (4 * t)) * ‖x‖ ^ 2)
      = (Real.pi / (1 / (4 * t))) ^ (3 / 2 : ℝ) := by
    have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℝ³) hb
    rw [hfr] at h
    simpa using h
  have hshape : ∀ x : ℝ³,
      heatK3 t x = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(1 / (4 * t)) * ‖x‖ ^ 2) := by
    intro x
    unfold heatK3
    rw [show -(1 / (4 * t)) * ‖x‖ ^ 2 = -‖x‖ ^ 2 / (4 * t) by ring]
  calc ∫ x : ℝ³, heatK3 t x
      = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ))
          * ∫ x : ℝ³, Real.exp (-(1 / (4 * t)) * ‖x‖ ^ 2) := by
        rw [← MeasureTheory.integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => hshape x)
    _ = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ))
          * (Real.pi / (1 / (4 * t))) ^ (3 / 2 : ℝ) := by rw [hgauss]
    _ = 1 := by
        have hdiv : Real.pi / (1 / (4 * t)) = 4 * Real.pi * t := by
          field_simp
        rw [hdiv]
        have hpos : (0 : ℝ) < 4 * Real.pi * t := by positivity
        rw [← Real.rpow_add hpos]
        norm_num

end Work.BoseFixR.LatGreen
