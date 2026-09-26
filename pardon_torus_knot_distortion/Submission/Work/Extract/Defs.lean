import Mathlib
import Submission.Work.Core.Torus

/-!
# Vocabulary for extracting the parametrised torus `ψ = Φ.Hinv 1 ∘ T`

Given an ambient isotopy `Φ` of `ℝ³` (the field `AmbientIsotopy` of `ChallengeDeps`),
the challenge hypothesis produces the map

  `ψ = fun p : ℝ × ℝ => Φ.Hinv 1 (Work.Core.torusMap p.1 p.2)`,

which is a smooth embedding of the parameter torus into `ℝ³` whose derivative is
uniformly bounded below.  This file collects the elementary vocabulary and facts
about `ψ` and about the two diffeomorphisms `Φ.H 1`, `Φ.Hinv 1`:

* `torusFun`, `torusFun_eq_toLp`, `torusFun_periodic_left/right`,
  `torusFun_contDiff`, `torusFun_differentiable`;
* `psiFun`, `psiFun_apply`, `psiFun_periodic_left/right`, `psiFun_contDiff`,
  `psiFun_differentiable`;
* `forwMap`, `invMap` and the chain-rule identities expressing that the two are
  inverse diffeomorphisms (`invMap_forwMap`, `forwMap_invMap`,
  `fderiv_invMap_comp_fderiv_forwMap`, `fderiv_forwMap_comp_fderiv_invMap`), and the
  resulting *expansion* estimate `norm_le_opNorm_mul_norm_fderiv`:
  `‖v‖ ≤ ‖fderiv (forwMap Φ) (invMap Φ q)‖ * ‖fderiv (invMap Φ) q v‖`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Extract

noncomputable section

/-! ### The standard torus parametrisation as a map on the plane -/

/-- The standard torus parametrisation, viewed as a map on the parameter plane. -/
def torusFun (p : ℝ × ℝ) : R3 := Work.Core.torusMap p.1 p.2

@[simp] theorem torusFun_apply (p : ℝ × ℝ) : torusFun p = Work.Core.torusMap p.1 p.2 := rfl

/-- The componentwise expression for `torusFun`. -/
noncomputable def torusCoord (p : ℝ × ℝ) : Fin 3 → ℝ :=
  ![(2 + Real.cos p.2) * Real.cos p.1, (2 + Real.cos p.2) * Real.sin p.1, Real.sin p.2]

/-- `torusFun p` is `WithLp.toLp 2` applied to the coordinate vector `torusCoord p`. -/
theorem torusFun_eq_toLp (p : ℝ × ℝ) :
    torusFun p = WithLp.toLp 2 (torusCoord p) := by
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

/-- The standard torus parametrisation is `2π`-periodic in the first variable. -/
theorem torusFun_periodic_left (x y : ℝ) :
    torusFun (x + 2 * Real.pi, y) = torusFun (x, y) :=
  Work.Core.torusMap_add_two_pi_left x y

/-- The standard torus parametrisation is `2π`-periodic in the second variable. -/
theorem torusFun_periodic_right (x y : ℝ) :
    torusFun (x, y + 2 * Real.pi) = torusFun (x, y) :=
  Work.Core.torusMap_add_two_pi_right x y

/-- The standard torus parametrisation is smooth. -/
theorem torusFun_contDiff : ContDiff ℝ (⊤ : ℕ∞) torusFun := by
  rw [show torusFun = fun p => WithLp.toLp 2 (torusCoord p) from
        funext torusFun_eq_toLp]
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> (simp [torusCoord]; fun_prop)

theorem torusFun_differentiable : Differentiable ℝ torusFun :=
  torusFun_contDiff.differentiable (by simp)

/-! ### The two diffeomorphisms of an ambient isotopy -/

/-- The forward map `x ↦ Φ.H 1 x` of an ambient isotopy at time `1`. -/
def forwMap (Φ : AmbientIsotopy) : R3 → R3 := fun x => Φ.H 1 x

/-- The inverse map `x ↦ Φ.Hinv 1 x` of an ambient isotopy at time `1`. -/
def invMap (Φ : AmbientIsotopy) : R3 → R3 := fun x => Φ.Hinv 1 x

@[simp] theorem forwMap_apply (Φ : AmbientIsotopy) (x : R3) : forwMap Φ x = Φ.H 1 x := rfl

@[simp] theorem invMap_apply (Φ : AmbientIsotopy) (x : R3) : invMap Φ x = Φ.Hinv 1 x := rfl

theorem forwMap_contDiff (Φ : AmbientIsotopy) : ContDiff ℝ (⊤ : ℕ∞) (forwMap Φ) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun x : R3 => ((1 : ℝ), x)) := by fun_prop
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : R3 => Φ.H 1 x) := Φ.smooth.comp h
  exact h2

theorem invMap_contDiff (Φ : AmbientIsotopy) : ContDiff ℝ (⊤ : ℕ∞) (invMap Φ) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun x : R3 => ((1 : ℝ), x)) := by fun_prop
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : R3 => Φ.Hinv 1 x) := Φ.smooth_inv.comp h
  exact h2

theorem forwMap_differentiable (Φ : AmbientIsotopy) : Differentiable ℝ (forwMap Φ) :=
  (forwMap_contDiff Φ).differentiable (by simp)

theorem invMap_differentiable (Φ : AmbientIsotopy) : Differentiable ℝ (invMap Φ) :=
  (invMap_contDiff Φ).differentiable (by simp)

theorem invMap_forwMap (Φ : AmbientIsotopy) : invMap Φ ∘ forwMap Φ = id := by
  funext x
  simp [invMap, forwMap, Φ.inv_left 1 x]

theorem forwMap_invMap (Φ : AmbientIsotopy) : forwMap Φ ∘ invMap Φ = id := by
  funext x
  simp [invMap, forwMap, Φ.inv_right 1 x]

/-- The chain rule identity expressing that `Φ.Hinv 1` and `Φ.H 1` are inverse. -/
theorem fderiv_invMap_comp_fderiv_forwMap (Φ : AmbientIsotopy) (x : R3) :
    (fderiv ℝ (invMap Φ) (forwMap Φ x)) ∘SL (fderiv ℝ (forwMap Φ) x) = 1 := by
  have h := fderiv_comp (𝕜 := ℝ) x (f := forwMap Φ) (g := invMap Φ)
    ((invMap_differentiable Φ) (forwMap Φ x)) ((forwMap_differentiable Φ) x)
  rw [show (invMap Φ ∘ forwMap Φ) = id from invMap_forwMap Φ, fderiv_id] at h
  exact h.symm

/-- The chain rule identity expressing that `Φ.H 1` and `Φ.Hinv 1` are inverse. -/
theorem fderiv_forwMap_comp_fderiv_invMap (Φ : AmbientIsotopy) (x : R3) :
    (fderiv ℝ (forwMap Φ) (invMap Φ x)) ∘SL (fderiv ℝ (invMap Φ) x) = 1 := by
  have h := fderiv_comp (𝕜 := ℝ) x (f := invMap Φ) (g := forwMap Φ)
    ((forwMap_differentiable Φ) (invMap Φ x)) ((invMap_differentiable Φ) x)
  rw [show (forwMap Φ ∘ invMap Φ) = id from forwMap_invMap Φ, fderiv_id] at h
  exact h.symm

/-- **Expansion estimate for the inverse of a diffeomorphism.**  For an ambient isotopy the
derivative of `Φ.Hinv 1` at `q` expands by at least the inverse of the operator norm of the
derivative of `Φ.H 1` at `invMap Φ q`. -/
theorem norm_le_opNorm_mul_norm_fderiv (Φ : AmbientIsotopy) (q v : R3) :
    ‖v‖ ≤ ‖fderiv ℝ (forwMap Φ) (invMap Φ q)‖ * ‖fderiv ℝ (invMap Φ) q v‖ := by
  have h := ContinuousLinearMap.le_opNorm (fderiv ℝ (forwMap Φ) (invMap Φ q))
    ((fderiv ℝ (invMap Φ) q) v)
  have hv : (fderiv ℝ (forwMap Φ) (invMap Φ q)) ((fderiv ℝ (invMap Φ) q) v) = v := by
    have := congrFun (congrArg DFunLike.coe (fderiv_forwMap_comp_fderiv_invMap Φ q)) v
    simpa using this
  rwa [hv] at h

/-- The derivative of `Φ.H 1` at `invMap Φ q` is nonzero. -/
theorem fderiv_forwMap_ne_zero (Φ : AmbientIsotopy) (q : R3) :
    fderiv ℝ (forwMap Φ) (invMap Φ q) ≠ 0 := by
  intro hzero
  have h := fderiv_forwMap_comp_fderiv_invMap Φ q
  rw [hzero, ContinuousLinearMap.zero_comp] at h
  exact one_ne_zero h.symm

/-! ### The parametrised torus `ψ = Φ.Hinv 1 ∘ T` -/

/-- The parametrised torus `ψ = Φ.Hinv 1 ∘ torusFun`. -/
def psiFun (Φ : AmbientIsotopy) (p : ℝ × ℝ) : R3 := invMap Φ (torusFun p)

@[simp] theorem psiFun_apply (Φ : AmbientIsotopy) (p : ℝ × ℝ) :
    psiFun Φ p = Φ.Hinv 1 (torusFun p) := rfl

theorem psiFun_periodic_left (Φ : AmbientIsotopy) (x y : ℝ) :
    psiFun Φ (x + 2 * Real.pi, y) = psiFun Φ (x, y) := by
  simp only [psiFun_apply]
  rw [torusFun_periodic_left]

theorem psiFun_periodic_right (Φ : AmbientIsotopy) (x y : ℝ) :
    psiFun Φ (x, y + 2 * Real.pi) = psiFun Φ (x, y) := by
  simp only [psiFun_apply]
  rw [torusFun_periodic_right]

theorem psiFun_contDiff (Φ : AmbientIsotopy) : ContDiff ℝ (⊤ : ℕ∞) (psiFun Φ) :=
  (invMap_contDiff Φ).comp torusFun_contDiff

theorem psiFun_differentiable (Φ : AmbientIsotopy) : Differentiable ℝ (psiFun Φ) :=
  (psiFun_contDiff Φ).differentiable (by simp)

/-- The chain rule form of the derivative of `ψ`. -/
theorem fderiv_psiFun (Φ : AmbientIsotopy) (p : ℝ × ℝ) :
    fderiv ℝ (psiFun Φ) p =
      (fderiv ℝ (invMap Φ) (torusFun p)) ∘SL (fderiv ℝ torusFun p) :=
  fderiv_comp (𝕜 := ℝ) p (f := torusFun) (g := invMap Φ)
    ((invMap_differentiable Φ) (torusFun p)) (torusFun_differentiable p)

end

end Work.Extract
