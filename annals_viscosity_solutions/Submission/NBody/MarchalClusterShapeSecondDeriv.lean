import Submission.NBody.MarchalClusterShapeLimit
import Submission.NBody.MarchalThirdDeriv

/-!
# The second derivative of the normalised configuration

Infrastructure for Ferrario–Terracini's `as:lim2` (`t² s̈ᵢ → 0`).

Writing `q = I_k^{1/2} s` for the centre-of-mass-relative configuration, the equation of motion is
`q̈ = cmRel(∇U)`, and differentiating `q = φ·s` twice (`φ = √(I_k ∘ x)`) gives

    `φ · s̈ = q̈ − φ''·s − 2φ'·ṡ`.

Every term on the right is controlled by the asymptotics of `I_k`, `İ_k`, `Ï_k` and by `as:lim1`.

Everything in this file is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators Topology
open InnerProductSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The equation of motion for the centre-of-mass-relative configuration of a cluster.** -/
theorem deriv_deriv_cmRel {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N} {ε t : ℝ}
    (ht : t ∈ Ioo (0:ℝ) ε)
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t)) :
    deriv (deriv (fun s : ℝ => cmRel m k (x s))) t = cmRel m k (∇_[m] (U m) (x t)) := by
  have hev : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hx s hs
  have hd : deriv (fun s : ℝ => cmRel m k (x s))
      =ᶠ[𝓝 t] (fun s : ℝ => cmRel m k (deriv x s)) := by
    filter_upwards [hev] with s hs
    exact (hasDerivAt_cmRel m k hs).deriv
  have hd2t : HasDerivAt (deriv x) (deriv (deriv x) t) t :=
    (hd2 t ht).congr_deriv (iteratedDeriv_two_eq_deriv_deriv x t)
  have h2 : HasDerivAt (fun s : ℝ => cmRel m k (deriv x s)) (cmRel m k (deriv (deriv x) t)) t :=
    hasDerivAt_cmRel m k hd2t
  rw [show deriv (deriv (fun s : ℝ => cmRel m k (x s))) t
      = deriv (fun s : ℝ => cmRel m k (deriv x s)) t from Filter.EventuallyEq.deriv_eq hd,
    h2.deriv, ← iteratedDeriv_two_eq_deriv_deriv x t, hode t ht]

/-- The centre-of-mass-relative configuration is `√(I_k)` times the normalised configuration. -/
lemma cmRel_eq_sqrt_smul_clusterShape {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N}
    (hI : 0 < clusterInertia m k x) :
    cmRel m k x = Real.sqrt (clusterInertia m k x) • clusterShape m k x := by
  rw [clusterShape, smul_smul, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hI)), one_smul]

/-- **The derivative of `√(I_k)` along a motion.** -/
lemma hasDerivAt_clusterSqrtInertia_curve {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {t : ℝ} (hJpos : 0 < clusterInertia m k (x t))
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s) :
    HasDerivAt (fun s : ℝ => Real.sqrt (clusterInertia m k (x s)))
      (deriv (fun s : ℝ => clusterInertia m k (x s)) t
        / (2 * Real.sqrt (clusterInertia m k (x t)))) t :=
  (hasDerivAt_clusterInertia_curve hx).sqrt (ne_of_gt hJpos)

/-- **The second derivative of `√(I_k)` along a motion:**
`φ'' = Ï/(2√I) − İ²/(4(√I)³)`. -/
lemma hasDerivAt_deriv_clusterSqrtInertia_curve {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε t : ℝ} (ht : t ∈ Ioo (0:ℝ) ε)
    (hpos : ∀ τ ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x τ))
    (hx : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x τ) τ)
    (hd2 : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x τ) τ) :
    HasDerivAt (deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s))))
      (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
          / (2 * Real.sqrt (clusterInertia m k (x t)))
        - (deriv (fun s : ℝ => clusterInertia m k (x s)) t) ^ 2
          / (4 * (Real.sqrt (clusterInertia m k (x t))) ^ 3)) t := by
  have hev : ∀ᶠ τ in 𝓝 t, HasDerivAt x (deriv x τ) τ := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
    exact hx τ hτ
  have hd2' : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (deriv (deriv x) τ) τ :=
    fun τ hτ => (hd2 τ hτ).congr_deriv (iteratedDeriv_two_eq_deriv_deriv x τ)
  have hu : HasDerivAt (fun τ : ℝ => deriv (fun s : ℝ => clusterInertia m k (x s)) τ)
      (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t) t :=
    hasDerivAt_deriv_clusterInertia_curve hev (hd2' t ht)
  have hφ := hasDerivAt_clusterSqrtInertia_curve (hpos t ht) hev
  have hv : HasDerivAt (fun τ : ℝ => 2 * Real.sqrt (clusterInertia m k (x τ)))
      (2 * (deriv (fun s : ℝ => clusterInertia m k (x s)) t
        / (2 * Real.sqrt (clusterInertia m k (x t))))) t := hφ.const_mul 2
  have hvne : 2 * Real.sqrt (clusterInertia m k (x t)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (hpos t ht)))
  have hdiv := hu.div hv hvne
  have heq : deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s)))
      =ᶠ[𝓝 t] (fun τ : ℝ => deriv (fun s : ℝ => clusterInertia m k (x s)) τ
        / (2 * Real.sqrt (clusterInertia m k (x τ)))) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
    have hevτ : ∀ᶠ s in 𝓝 τ, HasDerivAt x (deriv x s) s := by
      filter_upwards [isOpen_Ioo.mem_nhds hτ] with s hs
      exact hx s hs
    exact (hasDerivAt_clusterSqrtInertia_curve (hpos τ hτ) hevτ).deriv
  have hres := hdiv.congr_of_eventuallyEq heq
  have hval : (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
          * (2 * Real.sqrt (clusterInertia m k (x t)))
        - deriv (fun s : ℝ => clusterInertia m k (x s)) t
          * (2 * (deriv (fun s : ℝ => clusterInertia m k (x s)) t
              / (2 * Real.sqrt (clusterInertia m k (x t))))))
        / (2 * Real.sqrt (clusterInertia m k (x t))) ^ 2
      = deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
          / (2 * Real.sqrt (clusterInertia m k (x t)))
        - (deriv (fun s : ℝ => clusterInertia m k (x s)) t) ^ 2
          / (4 * (Real.sqrt (clusterInertia m k (x t))) ^ 3) := by
    field_simp
    ring
  exact hres.congr_deriv hval

/-- **The derivative of the coefficient `ψ = (√(I_k))⁻¹`** of the normalised configuration. -/
lemma hasDerivAt_clusterShapeCoeff {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε t : ℝ} (ht : t ∈ Ioo (0:ℝ) ε)
    (hpos : ∀ τ ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x τ))
    (hx : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x τ) τ) :
    HasDerivAt (fun τ : ℝ => (Real.sqrt (clusterInertia m k (x τ)))⁻¹)
      (-(deriv (fun τ : ℝ => Real.sqrt (clusterInertia m k (x τ))) t)
        / (Real.sqrt (clusterInertia m k (x t))) ^ 2) t := by
  have hev : ∀ᶠ τ in 𝓝 t, HasDerivAt x (deriv x τ) τ := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
    exact hx τ hτ
  have hφ := hasDerivAt_clusterSqrtInertia_curve (hpos t ht) hev
  have hne : Real.sqrt (clusterInertia m k (x t)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (hpos t ht))
  refine (hφ.inv hne).congr_deriv ?_
  rw [← hφ.deriv]

/-- **The second derivative of the coefficient `ψ`.** -/
lemma hasDerivAt_deriv_clusterShapeCoeff {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε t : ℝ} (ht : t ∈ Ioo (0:ℝ) ε)
    (hpos : ∀ τ ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x τ))
    (hx : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x τ) τ)
    (hd2 : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x τ) τ) :
    HasDerivAt
      (fun τ : ℝ => -(deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) τ)
        / (Real.sqrt (clusterInertia m k (x τ))) ^ 2)
      (-(deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t)
          / (Real.sqrt (clusterInertia m k (x t))) ^ 2
        + 2 * (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t) ^ 2
          / (Real.sqrt (clusterInertia m k (x t))) ^ 3) t := by
  have hev : ∀ᶠ τ in 𝓝 t, HasDerivAt x (deriv x τ) τ := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
    exact hx τ hτ
  have hφ := hasDerivAt_clusterSqrtInertia_curve (hpos t ht) hev
  have hφ2 := hasDerivAt_deriv_clusterSqrtInertia_curve ht hpos hx hd2
  have hne : Real.sqrt (clusterInertia m k (x t)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (hpos t ht))
  have hnum : HasDerivAt (fun τ : ℝ => -(deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) τ))
      (-(deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t)) t := by
    refine hφ2.neg.congr_deriv ?_
    rw [← hφ2.deriv]
  have hden : HasDerivAt ((fun τ : ℝ => Real.sqrt (clusterInertia m k (x τ)))
      * (fun τ : ℝ => Real.sqrt (clusterInertia m k (x τ))))
      (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t
          * Real.sqrt (clusterInertia m k (x t))
        + Real.sqrt (clusterInertia m k (x t))
          * deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t) t := by
    have h : HasDerivAt (fun τ : ℝ => Real.sqrt (clusterInertia m k (x τ)))
        (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t) t := by
      rw [hφ.deriv]; exact hφ
    exact h.mul h
  have hdne : ((fun τ : ℝ => Real.sqrt (clusterInertia m k (x τ)))
      * (fun τ : ℝ => Real.sqrt (clusterInertia m k (x τ)))) t ≠ 0 := by
    simp only [Pi.mul_apply]
    exact mul_ne_zero hne hne
  have hres := hnum.div hden hdne
  have hfun : (fun τ : ℝ => -(deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) τ)
        / (Real.sqrt (clusterInertia m k (x τ))) ^ 2)
      =ᶠ[𝓝 t] ((fun τ : ℝ => -(deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) τ))
        / ((fun τ : ℝ => Real.sqrt (clusterInertia m k (x τ)))
            * (fun τ : ℝ => Real.sqrt (clusterInertia m k (x τ))))) := by
    filter_upwards with τ
    simp [Pi.div_apply, Pi.mul_apply, pow_two]
  refine (hres.congr_of_eventuallyEq hfun).congr_deriv ?_
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- **The derivative of the normalised configuration, in coefficient form.**  With
`ψ = (√(I_k ∘ x))⁻¹` and `Ψ₁ = -(deriv φ)/(φ)²` (`φ = √(I_k ∘ x)`) this reads
`ṡ = Ψ₁ • q + ψ • q̇`. -/
lemma deriv_clusterShape_eq {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N} {ε t : ℝ}
    (ht : t ∈ Ioo (0:ℝ) ε)
    (hpos : ∀ τ ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x τ))
    (hx : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x τ) τ) :
    deriv (fun s : ℝ => clusterShape m k (x s))
      =ᶠ[𝓝 t] (fun τ : ℝ =>
        (-(deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) τ)
            / (Real.sqrt (clusterInertia m k (x τ))) ^ 2) • cmRel m k (x τ)
        + (Real.sqrt (clusterInertia m k (x τ)))⁻¹ • cmRel m k (deriv x τ)) := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
  have hevτ : ∀ᶠ s in 𝓝 τ, HasDerivAt x (deriv x s) s := by
    filter_upwards [isOpen_Ioo.mem_nhds hτ] with s hs
    exact hx s hs
  have h := hasDerivAt_clusterShape_curve (hpos τ hτ) hevτ
  have hφ' := (hasDerivAt_clusterSqrtInertia_curve (hpos τ hτ) hevτ).deriv
  have hcoef : -(deriv (fun s : ℝ => clusterInertia m k (x s)) τ
        / (2 * (Real.sqrt (clusterInertia m k (x τ))) ^ 3))
      = -(deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) τ)
          / (Real.sqrt (clusterInertia m k (x τ))) ^ 2 := by
    rw [hφ']
    field_simp
  change deriv (fun s : ℝ => clusterShape m k (x s)) τ
      = (-(deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) τ)
            / (Real.sqrt (clusterInertia m k (x τ))) ^ 2) • cmRel m k (x τ)
        + (Real.sqrt (clusterInertia m k (x τ)))⁻¹ • cmRel m k (deriv x τ)
  rw [h.deriv, hcoef, add_comm]

/-- **The second derivative of the normalised configuration.**  This is the Leibniz expansion of
`s = ψ • q` twice: `s̈ = Ψ₂ • q + Ψ₁ • q̇ + Ψ₁ • q̇ + ψ • q̈`, where `q̈ = cmRel(∇U)`. -/
theorem hasDerivAt_deriv_clusterShape {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε t : ℝ} (ht : t ∈ Ioo (0:ℝ) ε)
    (hpos : ∀ τ ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x τ))
    (hx : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x τ) τ)
    (hd2 : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x τ) τ)
    (hode : ∀ τ ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x τ = ∇_[m] (U m) (x τ)) :
    HasDerivAt (deriv (fun s : ℝ => clusterShape m k (x s)))
      ((-(deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t)
            / (Real.sqrt (clusterInertia m k (x t))) ^ 2
          + 2 * (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t) ^ 2
            / (Real.sqrt (clusterInertia m k (x t))) ^ 3) • cmRel m k (x t)
        + (-(deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t)
              / (Real.sqrt (clusterInertia m k (x t))) ^ 2) • cmRel m k (deriv x t)
        + (-(deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t)
              / (Real.sqrt (clusterInertia m k (x t))) ^ 2) • cmRel m k (deriv x t)
        + (Real.sqrt (clusterInertia m k (x t)))⁻¹ • cmRel m k (∇_[m] (U m) (x t))) t := by
  have hd2' : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (deriv (deriv x) τ) τ :=
    fun τ hτ => (hd2 τ hτ).congr_deriv (iteratedDeriv_two_eq_deriv_deriv x τ)
  have hq : HasDerivAt (fun τ : ℝ => cmRel m k (x τ)) (cmRel m k (deriv x t)) t :=
    hasDerivAt_cmRel m k (hx t ht)
  have hqv : HasDerivAt (fun τ : ℝ => cmRel m k (deriv x τ))
      (cmRel m k (∇_[m] (U m) (x t))) t := by
    refine (hasDerivAt_cmRel m k (hd2' t ht)).congr_deriv ?_
    rw [← iteratedDeriv_two_eq_deriv_deriv x t, hode t ht]
  have hψ := hasDerivAt_clusterShapeCoeff ht hpos hx
  have hΨ := hasDerivAt_deriv_clusterShapeCoeff ht hpos hx hd2
  have hLeib := (hΨ.smul hq).add (hψ.smul hqv)
  refine (hLeib.congr_of_eventuallyEq (deriv_clusterShape_eq ht hpos hx)).congr_deriv ?_
  abel

/-- **The `as:lim2` identity.**  `√(I_k) · s̈ = q̈ − φ''·s − 2φ'·ṡ`, the second-order Leibniz
expansion of `q = √(I_k)·s`. -/
theorem sqrtInertia_smul_deriv_deriv_clusterShape {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε t : ℝ} (ht : t ∈ Ioo (0:ℝ) ε)
    (hpos : ∀ τ ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x τ))
    (hx : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x τ) τ)
    (hd2 : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x τ) τ)
    (hode : ∀ τ ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x τ = ∇_[m] (U m) (x τ)) :
    Real.sqrt (clusterInertia m k (x t))
        • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t
      = cmRel m k (∇_[m] (U m) (x t))
        - deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t
            • clusterShape m k (x t)
        - (2 * deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t)
            • deriv (fun s : ℝ => clusterShape m k (x s)) t := by
  have hev : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hx s hs
  -- the first-order relation `deriv q =ᶠ φ' • s + φ • ṡ`
  have hleq : deriv (fun τ : ℝ => cmRel m k (x τ))
      =ᶠ[𝓝 t] (fun τ : ℝ => deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) τ
          • clusterShape m k (x τ)
        + Real.sqrt (clusterInertia m k (x τ))
          • deriv (fun s : ℝ => clusterShape m k (x s)) τ) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
    have hevτ : ∀ᶠ s in 𝓝 τ, HasDerivAt x (deriv x s) s := by
      filter_upwards [isOpen_Ioo.mem_nhds hτ] with s hs
      exact hx s hs
    have hφssτ : (fun υ : ℝ => cmRel m k (x υ))
        =ᶠ[𝓝 τ] (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)) • clusterShape m k (x υ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hτ] with υ hυ
      exact cmRel_eq_sqrt_smul_clusterShape (hpos υ hυ)
    have hφ1τ : HasDerivAt (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))
        (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) τ) τ := by
      have h := hasDerivAt_clusterSqrtInertia_curve (hpos τ hτ) hevτ
      exact h.congr_deriv h.deriv.symm
    have hss1τ : HasDerivAt (fun s : ℝ => clusterShape m k (x s))
        (deriv (fun s : ℝ => clusterShape m k (x s)) τ) τ := by
      have h := hasDerivAt_clusterShape_curve (hpos τ hτ) hevτ
      exact h.congr_deriv h.deriv.symm
    have h1 := hφ1τ.smul hss1τ
    have h1' : deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)) • clusterShape m k (x υ)) τ
        = Real.sqrt (clusterInertia m k (x τ)) • deriv (fun s : ℝ => clusterShape m k (x s)) τ
          + deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) τ • clusterShape m k (x τ) :=
      h1.deriv
    have hq_eq : deriv (fun υ : ℝ => cmRel m k (x υ)) τ
        = deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)) • clusterShape m k (x υ)) τ :=
      Filter.EventuallyEq.deriv_eq hφssτ
    rw [hq_eq, h1', add_comm]
  -- the two HasDerivAt facts at `t`, with the abstract derivative values
  have hφ1 : HasDerivAt (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))
      (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t) t := by
    have h := hasDerivAt_clusterSqrtInertia_curve (hpos t ht) hev
    exact h.congr_deriv h.deriv.symm
  have hφ2 : HasDerivAt (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))))
      (deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t) t := by
    have h := hasDerivAt_deriv_clusterSqrtInertia_curve ht hpos hx hd2
    exact h.congr_deriv h.deriv.symm
  have hss1 : HasDerivAt (fun s : ℝ => clusterShape m k (x s))
      (deriv (fun s : ℝ => clusterShape m k (x s)) t) t := by
    have h := hasDerivAt_clusterShape_curve (hpos t ht) hev
    exact h.congr_deriv h.deriv.symm
  have hss2 := hasDerivAt_deriv_clusterShape ht hpos hx hd2 hode
  have hss2' : HasDerivAt (deriv (fun s : ℝ => clusterShape m k (x s)))
      (deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t) t :=
    hss2.congr_deriv hss2.deriv.symm
  have hL : HasDerivAt (fun τ : ℝ => deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) τ
        • clusterShape m k (x τ)
      + Real.sqrt (clusterInertia m k (x τ)) • deriv (fun s : ℝ => clusterShape m k (x s)) τ)
      (deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t • clusterShape m k (x t)
        + deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t
            • deriv (fun s : ℝ => clusterShape m k (x s)) t
        + deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t
            • deriv (fun s : ℝ => clusterShape m k (x s)) t
        + Real.sqrt (clusterInertia m k (x t))
            • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t) t := by
    have h := (hφ2.smul hss1).add (hφ1.smul hss2')
    refine h.congr_deriv ?_
    abel
  have hval : deriv (deriv (fun τ : ℝ => cmRel m k (x τ))) t
      = deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t • clusterShape m k (x t)
        + deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t
            • deriv (fun s : ℝ => clusterShape m k (x s)) t
        + deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t
            • deriv (fun s : ℝ => clusterShape m k (x s)) t
        + Real.sqrt (clusterInertia m k (x t))
            • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t := by
    rw [show deriv (deriv (fun τ : ℝ => cmRel m k (x τ))) t
        = deriv (fun τ : ℝ => deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) τ
            • clusterShape m k (x τ)
          + Real.sqrt (clusterInertia m k (x τ))
            • deriv (fun s : ℝ => clusterShape m k (x s)) τ) t from
      Filter.EventuallyEq.deriv_eq hleq]
    exact hL.deriv
  have htwo : (2 * deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t)
        • deriv (fun s : ℝ => clusterShape m k (x s)) t
      = deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t
          • deriv (fun s : ℝ => clusterShape m k (x s)) t
        + deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t
          • deriv (fun s : ℝ => clusterShape m k (x s)) t := by
    rw [two_mul, add_smul]
  rw [← deriv_deriv_cmRel ht hx hd2 hode, hval, htwo]
  abel

/-- A bounded vector times `t^{2/3}` tends to `0` as `t → 0⁺`. -/
lemma tendsto_rpow_two_thirds_smul_zero_of_bounded {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ → F} {C ε : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hg : ∀ t ∈ Ioo (0:ℝ) ε, ‖g t‖ ≤ C) :
    Tendsto (fun t : ℝ => t ^ ((2:ℝ)/3) • g t) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
  have h2 : Tendsto (fun t : ℝ => ‖g t‖ * t ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) :=
    tendsto_mul_rpow_two_thirds_zero_of_bounded hε hC
      (fun t ht => by simpa using hg t ht)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine h2.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hε] with t ht
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_of_lt ht.1) _),
    mul_comm]

/-- The relative acceleration is bounded by a constant times the square of the potential
(`i ∈ k` bound of `exists_norm_accel_rel_le`, aggregated over the coordinates). -/
lemma exists_norm_cmRel_weightedGrad_le {m : Fin N → ℝ} {k : Finset (Fin N)} {ν : ℝ}
    (hm : ∀ i, 0 < m i) (hν : 0 < ν) (hk : k.Nonempty) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : EN E N, ClusterSeparatedWeak k x ν → WithoutCollisions x →
      1 ≤ clusterPotential m k x →
      ‖cmRel m k (∇_[m] (U m) x)‖ ≤ A * clusterPotential m k x ^ 2 := by
  obtain ⟨A, hApos, hA⟩ := exists_norm_accel_rel_le (E := E) (N := N) hm hν hk
  have hN : 0 < (N : ℝ) := by
    have h1 : 0 < k.card := Finset.card_pos.mpr hk
    have h2 : k.card ≤ N := by simpa using Finset.card_le_univ k
    exact_mod_cast lt_of_lt_of_le h1 h2
  refine ⟨Real.sqrt (N : ℝ) * A, by positivity, fun x hsep hnc hU => ?_⟩
  have hsq : ‖cmRel m k (∇_[m] (U m) x)‖ ^ 2
      ≤ (N : ℝ) * (A * clusterPotential m k x ^ 2) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc ∑ i : Fin N, ‖(cmRel m k (∇_[m] (U m) x)) i‖ ^ 2
        = ∑ i ∈ Finset.univ.filter (fun i : Fin N => i ∈ k),
            ‖(cmRel m k (∇_[m] (U m) x)) i‖ ^ 2 := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hi : i ∈ k
          · rw [if_pos hi]
          · rw [if_neg hi, cmRel_apply_of_notMem hi]
            simp
      _ = ∑ i ∈ k, ‖(cmRel m k (∇_[m] (U m) x)) i‖ ^ 2 := by
          congr 1
          ext i
          simp
      _ ≤ ∑ _i ∈ k, (A * clusterPotential m k x ^ 2) ^ 2 :=
          Finset.sum_le_sum fun i hi => by
            have h1 : ‖(∇_[m] (U m) x) i - clusterCM m k (∇_[m] (U m) x)‖
                ≤ A * clusterPotential m k x ^ 2 := hA x hsep hnc hU i hi
            have h2 : 0 ≤ A * clusterPotential m k x ^ 2 := by positivity
            have h3 : (cmRel m k (∇_[m] (U m) x)) i
                = (∇_[m] (U m) x) i - clusterCM m k (∇_[m] (U m) x) := cmRel_apply_of_mem hi
            rw [h3]
            nlinarith [h1, h2, norm_nonneg ((∇_[m] (U m) x) i - clusterCM m k (∇_[m] (U m) x))]
      _ = (k.card : ℝ) * (A * clusterPotential m k x ^ 2) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (A * clusterPotential m k x ^ 2) ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have : k.card ≤ N := by simpa using Finset.card_le_univ k
          exact_mod_cast this
  calc ‖cmRel m k (∇_[m] (U m) x)‖
      = Real.sqrt (‖cmRel m k (∇_[m] (U m) x)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((N : ℝ) * (A * clusterPotential m k x ^ 2) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (N : ℝ) * (A * clusterPotential m k x ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    _ = Real.sqrt (N : ℝ) * A * clusterPotential m k x ^ 2 := by ring

/-! ## Auxiliary `rpow` identities and the limit of `√(I_k)/t^{2/3}` -/

/-- For `t > 0` and `x ≥ 0`: `√x / t^{2/3} = √(x / t^{4/3})`. -/
lemma sqrt_div_rpow_two_thirds {x t : ℝ} (ht : 0 < t) (hx : 0 ≤ x) :
    Real.sqrt x / t ^ ((2:ℝ)/3) = Real.sqrt (x / t ^ ((4:ℝ)/3)) := by
  rw [Real.sqrt_div hx (t ^ ((4:ℝ)/3))]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
  norm_num

/-- For `t > 0` and `x > 0`: `(x / t^{4/3})^{-1/2} = t^{2/3}/√x`. -/
lemma rpow_neg_half_div_eq {x t : ℝ} (ht : 0 < t) (hx : 0 < x) :
    (x / t ^ ((4:ℝ)/3)) ^ (-((1:ℝ)/2)) = t ^ ((2:ℝ)/3) / Real.sqrt x := by
  rw [Real.rpow_neg (div_nonneg hx.le (Real.rpow_nonneg ht.le _)),
    Real.div_rpow hx.le (Real.rpow_nonneg ht.le _)]
  rw [show (t ^ ((4:ℝ)/3)) ^ ((1:ℝ)/2) = t ^ ((2:ℝ)/3) by
    rw [← Real.rpow_mul ht.le]; norm_num]
  rw [Real.sqrt_eq_rpow, inv_div]

/-- `√(f t)/t^{2/3} → √κ` whenever `f t / t^{4/3} → κ`. -/
lemma tendsto_sqrt_div_rpow_two_thirds {f : ℝ → ℝ} {κ ε : ℝ} (hε : 0 < ε) (hκ : 0 ≤ κ)
    (hfnn : ∀ t ∈ Ioo (0:ℝ) ε, 0 ≤ f t)
    (hf : Tendsto (fun t : ℝ => f t / t ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ)) :
    Tendsto (fun t : ℝ => Real.sqrt (f t) / t ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (Real.sqrt κ)) := by
  have h1 : Tendsto (fun t : ℝ => Real.sqrt (f t / t ^ ((4:ℝ)/3)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (Real.sqrt κ)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hf
  refine h1.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hε] with t ht
  exact (sqrt_div_rpow_two_thirds ht.1 (hfnn t ht)).symm

/-- `t^{2/3}/√(I_k) → 1/√κ` when `I_k/t^{4/3} → κ`. -/
lemma tendsto_rpow_two_thirds_div_sqrtInertia {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε κ : ℝ} (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε)
    (hκ : 0 < κ) (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hI : Tendsto (fun t : ℝ => clusterInertia m k (x t) / t ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ)) :
    Tendsto (fun t : ℝ => t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((Real.sqrt κ)⁻¹)) := by
  have h := hI.rpow_const (p := -((1:ℝ)/2)) (Or.inl (ne_of_gt hκ))
  have hval : κ ^ (-((1:ℝ)/2)) = (Real.sqrt κ)⁻¹ := by
    rw [Real.rpow_neg hκ.le, Real.sqrt_eq_rpow]
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hε] with t ht
  exact rpow_neg_half_div_eq ht.1 (clusterInertia_pos hm hk2 (hnc t ht))

/-- **Boundedness of the `ṡ` coefficient.**  `t^{1/3}·φ'` is eventually bounded, where
`φ' = deriv √(I_k ∘ x)`. -/
lemma exists_bound_rpow_third_deriv_sqrtInertia {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε κ : ℝ} (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε)
    (hκ : 0 < κ) (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hIn : Tendsto (fun t : ℝ => clusterInertia m k (x t) / t ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hDn : Tendsto (fun t : ℝ => deriv (fun s : ℝ => clusterInertia m k (x s)) t
      / t ^ ((1:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/3 * κ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      |t ^ ((1:ℝ)/3) * deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s))) t| ≤ C := by
  have hA := tendsto_rpow_two_thirds_div_sqrtInertia hm hk2 hε hκ hnc hIn
  set L : ℝ := ((4:ℝ)/3 * κ) * (Real.sqrt κ)⁻¹ / 2 with hL
  have hlim : Tendsto (fun t : ℝ =>
      (deriv (fun s : ℝ => clusterInertia m k (x s)) t / t ^ ((1:ℝ)/3))
        * (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t))) / 2)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds L) := by
    have h := hDn.mul hA
    have h' : Tendsto (fun t : ℝ => (deriv (fun s : ℝ => clusterInertia m k (x s)) t
          / t ^ ((1:ℝ)/3)) * (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t))))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (((4:ℝ)/3 * κ) * (Real.sqrt κ)⁻¹)) := by
      simpa only [Pi.mul_apply] using h
    have h2 : Tendsto (fun t : ℝ => ((deriv (fun s : ℝ => clusterInertia m k (x s)) t
          / t ^ ((1:ℝ)/3)) * (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t)))) / 2)
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((((4:ℝ)/3 * κ) * (Real.sqrt κ)⁻¹) / 2)) :=
      h'.div_const 2
    simpa only [hL] using h2
  have heq : (fun t : ℝ =>
      t ^ ((1:ℝ)/3) * deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s))) t)
      =ᶠ[nhdsWithin (0:ℝ) (Ioi 0)] (fun t : ℝ =>
        (deriv (fun s : ℝ => clusterInertia m k (x s)) t / t ^ ((1:ℝ)/3))
          * (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t))) / 2) := by
    filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    have hev : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hx s hs
    rw [(hasDerivAt_clusterSqrtInertia_curve (clusterInertia_pos hm hk2 (hnc t ht)) hev).deriv]
    have ht13 : t ^ ((1:ℝ)/3) * t ^ ((1:ℝ)/3) = t ^ ((2:ℝ)/3) := by
      rw [← Real.rpow_add ht.1]; norm_num
    rw [show t ^ ((2:ℝ)/3) = t ^ ((1:ℝ)/3) * t ^ ((1:ℝ)/3) from ht13.symm]
    field_simp
  have hnorm : Tendsto (fun t : ℝ =>
      |(deriv (fun s : ℝ => clusterInertia m k (x s)) t / t ^ ((1:ℝ)/3))
        * (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t))) / 2|)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds |L|) := by
    simpa only [Real.norm_eq_abs] using hlim.norm
  refine ⟨|L| + 1, by positivity, ?_⟩
  filter_upwards [heq, hnorm.eventually (isOpen_Iio.mem_nhds (by linarith [abs_nonneg L] : |L| < |L| + 1))]
    with t heqt hbnd
  rw [heqt]
  exact le_of_lt hbnd

/-- **Boundedness of the `q̈` term of `t²s̈`.**  `(t²/√(I_k))·cmRel(∇U)` stays bounded, by
`exists_norm_cmRel_weightedGrad_le` and `U_k·t^{2/3} → (2/9)κ`. -/
lemma exists_bound_div_sqrtInertia_mul_cmRel_grad {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε κ ν : ℝ} (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε)
    (hκ : 0 < κ) (hν : 0 < ν) (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparatedWeak k (x t) ν)
    (hIn : Tendsto (fun t : ℝ => clusterInertia m k (x t) / t ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hUn : Tendsto (fun t : ℝ => clusterPotential m k (x t) * t ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((2:ℝ)/9 * κ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      ‖(t ^ 2 / Real.sqrt (clusterInertia m k (x t))) • cmRel m k (∇_[m] (U m) (x t))‖ ≤ C := by
  have hkne : k.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨A, hApos, hA⟩ := exists_norm_cmRel_weightedGrad_le (E := E) (N := N) hm hν hkne
  have hA1 := tendsto_rpow_two_thirds_div_sqrtInertia hm hk2 hε hκ hnc hIn
  have hlim : Tendsto (fun t : ℝ => (clusterPotential m k (x t) * t ^ ((2:ℝ)/3)) ^ 2
      * (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t))))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (((2:ℝ)/9 * κ) ^ 2 * (Real.sqrt κ)⁻¹)) := by
    have h := (hUn.pow 2).mul hA1
    simpa only [Pi.mul_apply] using h
  set L2 : ℝ := ((2:ℝ)/9 * κ) ^ 2 * (Real.sqrt κ)⁻¹ with hL2
  have hL2nn : 0 ≤ L2 := by rw [hL2]; positivity
  -- eventually `U ≥ 1`
  have ht23 : Tendsto (fun t : ℝ => t ^ ((2:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) :=
    tendsto_rpow_two_thirds_nhdsWithin_zero
  have hevsmall : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      t ^ ((2:ℝ)/3) < (2:ℝ)/9 * κ / 2 :=
    ht23.eventually (isOpen_Iio.mem_nhds (by simp only [Set.mem_Iio]; positivity))
  have hevbig : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      (2:ℝ)/9 * κ / 2 < clusterPotential m k (x t) * t ^ ((2:ℝ)/3) :=
    hUn.eventually (isOpen_Ioi.mem_nhds (by linarith : (2:ℝ)/9 * κ / 2 < (2:ℝ)/9 * κ))
  have hevU : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0), 1 ≤ clusterPotential m k (x t) := by
    filter_upwards [hevsmall, hevbig, Ioo_mem_nhdsGT hε] with t hs hb ht
    have ht0 : 0 < t := ht.1
    have h1 : 1 < ((2:ℝ)/9 * κ / 2) / t ^ ((2:ℝ)/3) := by
      rw [lt_div_iff₀ (Real.rpow_pos_of_pos ht0 _)]
      linarith [hs]
    have h2 : ((2:ℝ)/9 * κ / 2) / t ^ ((2:ℝ)/3)
        < clusterPotential m k (x t) * t ^ ((2:ℝ)/3) / t ^ ((2:ℝ)/3) := by
      rw [div_lt_div_iff_of_pos_right (Real.rpow_pos_of_pos ht0 _)]
      exact hb
    have h3 : clusterPotential m k (x t) * t ^ ((2:ℝ)/3) / t ^ ((2:ℝ)/3)
        = clusterPotential m k (x t) := by
      field_simp
    linarith [h1, h2, h3.le]
  have hevL : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      (clusterPotential m k (x t) * t ^ ((2:ℝ)/3)) ^ 2
        * (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t))) < L2 + 1 := by
    have h := hlim.eventually (isOpen_Iio.mem_nhds (by linarith : L2 < L2 + 1))
    filter_upwards [h] with t ht
    rwa [hL2]
  refine ⟨A * (L2 + 1), by positivity, ?_⟩
  filter_upwards [hevU, hevL, Ioo_mem_nhdsGT hε] with t hU1 hLbound ht
  have ht0 : 0 < t := ht.1
  have hIpos : 0 < clusterInertia m k (x t) := clusterInertia_pos hm hk2 (hnc t ht)
  have hsqrtpos : 0 < Real.sqrt (clusterInertia m k (x t)) := Real.sqrt_pos.mpr hIpos
  have hq : ‖cmRel m k (∇_[m] (U m) (x t))‖
      ≤ A * (clusterPotential m k (x t)) ^ 2 :=
    hA (x t) (hsep t ht) (hnc t ht) hU1
  have ht2 : t ^ 2 = (t ^ ((2:ℝ)/3)) ^ 2 * t ^ ((2:ℝ)/3) := by
    rw [← Real.rpow_natCast (t ^ ((2:ℝ)/3)) 2, ← Real.rpow_mul ht0.le, ← Real.rpow_add ht0]
    norm_num
  have hkey : t ^ 2 / Real.sqrt (clusterInertia m k (x t))
        * (clusterPotential m k (x t)) ^ 2
      = (clusterPotential m k (x t) * t ^ ((2:ℝ)/3)) ^ 2
        * (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t))) := by
    rw [ht2, mul_pow]
    ring
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity) hsqrtpos.le)]
  calc t ^ 2 / Real.sqrt (clusterInertia m k (x t))
        * ‖cmRel m k (∇_[m] (U m) (x t))‖
      ≤ t ^ 2 / Real.sqrt (clusterInertia m k (x t))
          * (A * (clusterPotential m k (x t)) ^ 2) :=
        mul_le_mul_of_nonneg_left hq (div_nonneg (by positivity) hsqrtpos.le)
    _ = A * (t ^ 2 / Real.sqrt (clusterInertia m k (x t))
          * (clusterPotential m k (x t)) ^ 2) := by
        ring
    _ = A * ((clusterPotential m k (x t) * t ^ ((2:ℝ)/3)) ^ 2
            * (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t)))) := by
        rw [hkey]
    _ ≤ A * (L2 + 1) :=
        mul_le_mul_of_nonneg_left (le_of_lt hLbound) hApos.le

/-- **Boundedness of the `s̈` coefficient.**  `t^{4/3}·φ''` is eventually bounded, where
`φ'' = deriv (deriv √(I_k ∘ x))`. -/
lemma exists_bound_rpow_four_thirds_deriv_deriv_sqrtInertia {m : Fin N → ℝ}
    {k : Finset (Fin N)} {x : ℝ → EN E N} {ε κ : ℝ} (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card)
    (hε : 0 < ε) (hκ : 0 < κ) (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hIn : Tendsto (fun t : ℝ => clusterInertia m k (x t) / t ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hDn : Tendsto (fun t : ℝ => deriv (fun s : ℝ => clusterInertia m k (x s)) t
      / t ^ ((1:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/3 * κ)))
    (hSec : Tendsto (fun t : ℝ => deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
      * t ^ ((2:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/9 * κ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      |t ^ ((4:ℝ)/3)
        * deriv (deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s)))) t| ≤ C := by
  have hA := tendsto_rpow_two_thirds_div_sqrtInertia hm hk2 hε hκ hnc hIn
  set L3 : ℝ := ((4:ℝ)/9 * κ) * (Real.sqrt κ)⁻¹ / 2
    - ((4:ℝ)/3 * κ) ^ 2 * ((Real.sqrt κ)⁻¹) ^ 3 / 4 with hL3
  have hlim : Tendsto (fun t : ℝ =>
      (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t * t ^ ((2:ℝ)/3))
          * (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t))) / 2
        - (deriv (fun s : ℝ => clusterInertia m k (x s)) t / t ^ ((1:ℝ)/3)) ^ 2
          * (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t))) ^ 3 / 4)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds L3) := by
    have h1 : Tendsto (fun t : ℝ =>
        (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t * t ^ ((2:ℝ)/3))
          * (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t))) / 2)
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (((4:ℝ)/9 * κ) * (Real.sqrt κ)⁻¹ / 2)) := by
      have h := (hSec.mul hA).div_const 2
      simpa only [Pi.mul_apply] using h
    have h2 : Tendsto (fun t : ℝ =>
        (deriv (fun s : ℝ => clusterInertia m k (x s)) t / t ^ ((1:ℝ)/3)) ^ 2
          * (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t))) ^ 3 / 4)
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (((4:ℝ)/3 * κ) ^ 2 * ((Real.sqrt κ)⁻¹) ^ 3 / 4)) := by
      have h := ((hDn.pow 2).mul (hA.pow 3)).div_const 4
      simpa only [Pi.mul_apply, Pi.pow_apply] using h
    have h := h1.sub h2
    simpa only [hL3] using h
  have heq : (fun t : ℝ => t ^ ((4:ℝ)/3)
        * deriv (deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s)))) t)
      =ᶠ[nhdsWithin (0:ℝ) (Ioi 0)] (fun t : ℝ =>
        (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t * t ^ ((2:ℝ)/3))
            * (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t))) / 2
          - (deriv (fun s : ℝ => clusterInertia m k (x s)) t / t ^ ((1:ℝ)/3)) ^ 2
            * (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t))) ^ 3 / 4) := by
    filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    have ht0 : 0 < t := ht.1
    have hIpos : 0 < clusterInertia m k (x t) := clusterInertia_pos hm hk2 (hnc t ht)
    have hev : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hx s hs
    have hpos' : ∀ τ ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x τ) :=
      fun τ hτ => clusterInertia_pos hm hk2 (hnc τ hτ)
    set a : ℝ := t ^ ((2:ℝ)/3) with hadef
    set b : ℝ := t ^ ((1:ℝ)/3) with hbdef
    have han : a ≠ 0 := by rw [hadef]; exact ne_of_gt (Real.rpow_pos_of_pos ht0 _)
    have hbn : b ≠ 0 := by rw [hbdef]; exact ne_of_gt (Real.rpow_pos_of_pos ht0 _)
    have hs : Real.sqrt (clusterInertia m k (x t)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hIpos)
    have ha : a ^ 2 = t ^ ((4:ℝ)/3) := by
      rw [hadef, ← Real.rpow_natCast (t ^ ((2:ℝ)/3)) 2, ← Real.rpow_mul ht0.le]
      norm_num
    have hb : b ^ 2 = a := by
      rw [hbdef, hadef, ← Real.rpow_natCast (t ^ ((1:ℝ)/3)) 2, ← Real.rpow_mul ht0.le]
      norm_num
    rw [(hasDerivAt_deriv_clusterSqrtInertia_curve ht hpos' hx hd2).deriv, ← ha]
    rw [div_pow, div_pow, hb]
    field_simp
  have hnorm : Tendsto (fun t : ℝ =>
      |(deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t * t ^ ((2:ℝ)/3))
          * (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t))) / 2
        - (deriv (fun s : ℝ => clusterInertia m k (x s)) t / t ^ ((1:ℝ)/3)) ^ 2
          * (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t))) ^ 3 / 4|)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds |L3|) := by
    simpa only [Real.norm_eq_abs] using hlim.norm
  refine ⟨|L3| + 1, by positivity, ?_⟩
  filter_upwards [heq, hnorm.eventually
    (isOpen_Iio.mem_nhds (by linarith [abs_nonneg L3] : |L3| < |L3| + 1))] with t heqt hbnd
  rw [heqt]
  exact le_of_lt hbnd

/-- The normalised configuration is bounded: `‖s‖² ≤ 1/c` whenever `m ≥ c` on the cluster. -/
lemma norm_clusterShape_sq_le {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N} {c : ℝ}
    (hc : 0 < c) (hmin : ∀ i ∈ k, c ≤ m i) (hIpos : 0 < clusterInertia m k x) :
    ‖clusterShape m k x‖ ^ 2 ≤ 1 / c := by
  rw [PiLp.norm_sq_eq_of_L2]
  calc ∑ i : Fin N, ‖(clusterShape m k x) i‖ ^ 2
      = ∑ i ∈ Finset.univ.filter (fun i : Fin N => i ∈ k),
          ‖(clusterShape m k x) i‖ ^ 2 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : i ∈ k
        · rw [if_pos hi]
        · rw [if_neg hi, clusterShape_apply, cmRel_apply_of_notMem hi, smul_zero, norm_zero]
          simp
      _ = ∑ i ∈ k, ‖(clusterShape m k x) i‖ ^ 2 := by
        congr 1; ext i; simp
      _ ≤ ∑ i ∈ k, (m i * ‖(clusterShape m k x) i‖ ^ 2) / c := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [le_div_iff₀ hc]
        nlinarith [hmin i hi, sq_nonneg ‖(clusterShape m k x) i‖]
      _ = (∑ i ∈ k, m i * ‖(clusterShape m k x) i‖ ^ 2) / c := by
        rw [← Finset.sum_div]
      _ = clusterKineticSq m k (clusterShape m k x) / c := rfl
      _ = 1 / c := by rw [clusterKineticSq_clusterShape hIpos]

/-- **The boundedness of `t²s̈`** (the first half of Ferrario–Terracini's `as:lim2`). -/
theorem exists_bound_mul_sq_deriv_deriv_clusterShape {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε C ν Cv κ : ℝ}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hC : 0 < C) (hν : 0 < ν)
    (hCv : 0 ≤ Cv) (hκ : 0 < κ)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hE : ∀ t ∈ Ioo (0:ℝ) ε, |clusterRelEnergy m k (x t) (deriv x t)| ≤ C)
    (hW : ∀ t ∈ Ioo (0:ℝ) ε, |crossWork m k (x t) (cmRel m k (x t))| ≤ C)
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hd3 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparatedWeak k (x t) ν)
    (hv : ∀ t ∈ Ioo (0:ℝ) ε, ∀ j ∉ k,
      ‖deriv x t j‖ ≤ Cv * Real.sqrt (clusterPotential m k (x t)))
    (hI : Tendsto (fun t : ℝ => clusterInertia m k (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    (hIn : Tendsto (fun t : ℝ => clusterInertia m k (x t) / t ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hDn : Tendsto (fun t : ℝ => deriv (fun s : ℝ => clusterInertia m k (x s)) t
      / t ^ ((1:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/3 * κ)))
    (hSec : Tendsto (fun t : ℝ => deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
      * t ^ ((2:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/9 * κ)))
    (hUn : Tendsto (fun t : ℝ => clusterPotential m k (x t) * t ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((2:ℝ)/9 * κ))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      ‖t ^ 2 • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t‖ ≤ K := by
  have hpos' : ∀ τ ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x τ) :=
    fun τ hτ => clusterInertia_pos hm hk2 (hnc τ hτ)
  obtain ⟨c, hcpos, hcmin⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i ∈ k, c ≤ m i := by
    obtain ⟨i0, hi0⟩ := Finset.card_pos.mp (by omega : 0 < k.card)
    obtain ⟨i1, hi1, hle⟩ := Finset.exists_min_image k m ⟨i0, hi0⟩
    exact ⟨m i1, hm i1, fun i hi => hle i hi⟩
  obtain ⟨C1, hC1nn, hC1⟩ :=
    exists_bound_div_sqrtInertia_mul_cmRel_grad hm hk2 hε hκ hν hnc hsep hIn hUn
  obtain ⟨C2, hC2nn, hC2⟩ :=
    exists_bound_rpow_four_thirds_deriv_deriv_sqrtInertia hm hk2 hε hκ hnc hx hd2 hIn hDn hSec
  obtain ⟨C3, hC3nn, hC3⟩ :=
    exists_bound_rpow_third_deriv_sqrtInertia hm hk2 hε hκ hnc hx hIn hDn
  have hA := tendsto_rpow_two_thirds_div_sqrtInertia hm hk2 hε hκ hnc hIn
  have hC0 : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t)) ≤ ((Real.sqrt κ)⁻¹ + 1) := by
    have h : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
        t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t)) < (Real.sqrt κ)⁻¹ + 1 :=
      hA.eventually (isOpen_Iio.mem_nhds
        (by simp only [Set.mem_Iio]; linarith [inv_nonneg.mpr (Real.sqrt_nonneg κ)]))
    filter_upwards [h] with t ht
    exact le_of_lt ht
  have hsnorm : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      ‖clusterShape m k (x t)‖ ≤ Real.sqrt (1 / c) := by
    filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    calc ‖clusterShape m k (x t)‖ = Real.sqrt (‖clusterShape m k (x t)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (1 / c) := Real.sqrt_le_sqrt (norm_clusterShape_sq_le hcpos hcmin (hpos' t ht))
  have hts : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      ‖t • deriv (fun s : ℝ => clusterShape m k (x s)) t‖ ≤ 1 := by
    have h := (tendsto_mul_deriv_clusterShape (m := m) (k := k) (x := x) (ε := ε) (C := C)
      (ν := ν) (Cv := Cv) hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode hsep hv hI).norm
    filter_upwards [h.eventually (isOpen_Iio.mem_nhds (by simp : ‖(0 : EN E N)‖ < 1))]
      with t ht
    exact le_of_lt ht
  -- the two coefficient identities
  have hcoef2 : ∀ t ∈ Ioo (0:ℝ) ε,
      |t ^ 2 / Real.sqrt (clusterInertia m k (x t))
        * deriv (deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s)))) t|
      = (t ^ ((4:ℝ)/3)
          * |deriv (deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s)))) t|)
        * (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t))) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    rw [abs_mul, abs_of_nonneg (div_nonneg (by positivity) (Real.sqrt_nonneg _))]
    rw [show t ^ 2 = t ^ ((4:ℝ)/3) * t ^ ((2:ℝ)/3) by
      rw [← Real.rpow_add ht0]; norm_num]
    rw [div_eq_mul_inv]
    ring
  have hcoef3 : ∀ t ∈ Ioo (0:ℝ) ε,
      |t ^ 2 / Real.sqrt (clusterInertia m k (x t))
          * (2 * deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s))) t)|
        * ‖deriv (fun s : ℝ => clusterShape m k (x s)) t‖
      = 2 * (t ^ ((1:ℝ)/3)
            * |deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s))) t|)
          * (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t)))
          * ‖t • deriv (fun s : ℝ => clusterShape m k (x s)) t‖ := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hsn : ‖deriv (fun s : ℝ => clusterShape m k (x s)) t‖
        = ‖t • deriv (fun s : ℝ => clusterShape m k (x s)) t‖ * t⁻¹ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, mul_comm t, mul_assoc,
        mul_inv_cancel₀ (ne_of_gt ht0), mul_one]
    rw [abs_mul, abs_of_nonneg (div_nonneg (by positivity) (Real.sqrt_nonneg _)), abs_mul,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    rw [show t ^ 2 = t ^ ((1:ℝ)/3) * t ^ ((2:ℝ)/3) * t by
      rw [← Real.rpow_add ht0, show ((1:ℝ)/3 + (2:ℝ)/3) = (1:ℝ) by norm_num, Real.rpow_one]
      ring]
    rw [hsn, div_eq_mul_inv]
    field_simp
  -- the rearranged identity
  have hId : ∀ t ∈ Ioo (0:ℝ) ε,
      t ^ 2 • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t
        = (t ^ 2 / Real.sqrt (clusterInertia m k (x t))) • cmRel m k (∇_[m] (U m) (x t))
          - ((t ^ 2 / Real.sqrt (clusterInertia m k (x t)))
              * deriv (deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s)))) t)
            • clusterShape m k (x t)
          - ((t ^ 2 / Real.sqrt (clusterInertia m k (x t)))
              * (2 * deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s))) t))
            • deriv (fun s : ℝ => clusterShape m k (x s)) t := by
    intro t ht
    have hne : Real.sqrt (clusterInertia m k (x t)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (hpos' t ht))
    have hid := sqrtInertia_smul_deriv_deriv_clusterShape ht hpos' hx hd2 hode
    calc t ^ 2 • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t
        = (t ^ 2 / Real.sqrt (clusterInertia m k (x t)))
            • (Real.sqrt (clusterInertia m k (x t))
                • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t) := by
          rw [smul_smul, div_mul_cancel₀ _ hne]
      _ = (t ^ 2 / Real.sqrt (clusterInertia m k (x t)))
            • (cmRel m k (∇_[m] (U m) (x t))
                - deriv (deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s)))) t
                    • clusterShape m k (x t)
                - (2 * deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s))) t)
                    • deriv (fun s : ℝ => clusterShape m k (x s)) t) := by
          rw [hid]
      _ = (t ^ 2 / Real.sqrt (clusterInertia m k (x t))) • cmRel m k (∇_[m] (U m) (x t))
          - ((t ^ 2 / Real.sqrt (clusterInertia m k (x t)))
              * deriv (deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s)))) t)
            • clusterShape m k (x t)
          - ((t ^ 2 / Real.sqrt (clusterInertia m k (x t)))
              * (2 * deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s))) t))
            • deriv (fun s : ℝ => clusterShape m k (x s)) t := by
          simp only [smul_sub, smul_smul]
  refine ⟨C1 + C2 * ((Real.sqrt κ)⁻¹ + 1) * Real.sqrt (1 / c) + 2 * C3 * ((Real.sqrt κ)⁻¹ + 1), by positivity, ?_⟩
  filter_upwards [hC1, hC2, hC3, hC0, hsnorm, hts, Ioo_mem_nhdsGT hε]
    with t h1 h2 h3 h4 h5 h6 ht
  have ht0 : 0 < t := ht.1
  have hsqnn : 0 ≤ Real.sqrt (clusterInertia m k (x t)) := Real.sqrt_nonneg _
  have hcnn : 0 ≤ t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t)) :=
    div_nonneg (Real.rpow_nonneg ht0.le _) hsqnn
  have h2' : t ^ ((4:ℝ)/3)
      * |deriv (deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s)))) t| ≤ C2 := by
    have := h2
    rwa [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ ((4:ℝ)/3))] at this
  have h3' : t ^ ((1:ℝ)/3)
      * |deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s))) t| ≤ C3 := by
    have := h3
    rwa [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ ((1:ℝ)/3))] at this
  have hb2 : ‖((t ^ 2 / Real.sqrt (clusterInertia m k (x t)))
        * deriv (deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s)))) t)
        • clusterShape m k (x t)‖ ≤ C2 * ((Real.sqrt κ)⁻¹ + 1) * Real.sqrt (1 / c) := by
    rw [norm_smul, Real.norm_eq_abs, hcoef2 t ht]
    refine mul_le_mul ?_ h5 (norm_nonneg _) (by positivity)
    exact mul_le_mul h2' h4 hcnn hC2nn
  have hb3 : ‖((t ^ 2 / Real.sqrt (clusterInertia m k (x t)))
        * (2 * deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s))) t))
        • deriv (fun s : ℝ => clusterShape m k (x s)) t‖ ≤ 2 * C3 * ((Real.sqrt κ)⁻¹ + 1) := by
    rw [norm_smul, Real.norm_eq_abs, hcoef3 t ht]
    calc 2 * (t ^ ((1:ℝ)/3)
            * |deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s))) t|)
          * (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t)))
          * ‖t • deriv (fun s : ℝ => clusterShape m k (x s)) t‖
        ≤ 2 * (C3 * ((Real.sqrt κ)⁻¹ + 1)) * 1 := by
          have hstep : t ^ ((1:ℝ)/3)
                * |deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s))) t|
                * (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t)))
              ≤ C3 * ((Real.sqrt κ)⁻¹ + 1) := mul_le_mul h3' h4 hcnn hC3nn
          have hstep2 : 2 * (t ^ ((1:ℝ)/3)
                * |deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s))) t|
                * (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t))))
              ≤ 2 * (C3 * ((Real.sqrt κ)⁻¹ + 1)) :=
            mul_le_mul_of_nonneg_left hstep (by norm_num : (0:ℝ) ≤ 2)
          refine le_trans (le_of_eq ?_) (mul_le_mul hstep2 h6 (norm_nonneg _) (by positivity))
          ring
      _ = 2 * C3 * ((Real.sqrt κ)⁻¹ + 1) := by ring
  calc ‖t ^ 2 • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t‖
      = ‖(t ^ 2 / Real.sqrt (clusterInertia m k (x t))) • cmRel m k (∇_[m] (U m) (x t))
          - ((t ^ 2 / Real.sqrt (clusterInertia m k (x t)))
              * deriv (deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s)))) t)
            • clusterShape m k (x t)
          - ((t ^ 2 / Real.sqrt (clusterInertia m k (x t)))
              * (2 * deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s))) t))
            • deriv (fun s : ℝ => clusterShape m k (x s)) t‖ := by
        rw [hId t ht]
    _ ≤ C1 + C2 * ((Real.sqrt κ)⁻¹ + 1) * Real.sqrt (1 / c) + 2 * C3 * ((Real.sqrt κ)⁻¹ + 1) := by
        refine le_trans (norm_sub_le _ _) (add_le_add ?_ hb3)
        exact le_trans (norm_sub_le _ _) (add_le_add h1 hb2)

/-- **Boundedness of `t^(5/3) times the jolt of `I_k`.**  The Sundman refinement
`|I_k'| ≤ e (Ï_k)^(5/2)` together with `Ï_k t^(2/3) → (4/9)κ` gives
`t^(5/3) |I_k'| ≤ e (Ï_k t^(2/3))^(5/2)`. -/
lemma exists_bound_rpow_five_thirds_third_deriv_clusterInertia {m : Fin N → ℝ}
    {k : Finset (Fin N)} {x : ℝ → EN E N} {ε C ν Cv κ : ℝ}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hC : 0 < C) (hν : 0 < ν)
    (hCv : 0 ≤ Cv) (hκ : 0 < κ)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hE : ∀ t ∈ Ioo (0:ℝ) ε, |clusterRelEnergy m k (x t) (deriv x t)| ≤ C)
    (hW : ∀ t ∈ Ioo (0:ℝ) ε, |crossWork m k (x t) (cmRel m k (x t))| ≤ C)
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hd3 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparatedWeak k (x t) ν)
    (hv : ∀ t ∈ Ioo (0:ℝ) ε, ∀ j ∉ k,
      ‖deriv x t j‖ ≤ Cv * Real.sqrt (clusterPotential m k (x t)))
    (hI : Tendsto (fun t : ℝ => clusterInertia m k (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    (hSec : Tendsto (fun t : ℝ => deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
      * t ^ ((2:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/9 * κ))) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      |t ^ ((5:ℝ)/3) * deriv (deriv (deriv (fun s : ℝ => clusterInertia m k (x s)))) t| ≤ C' := by
  obtain ⟨e, hepos, ε₁, hε₁pos, hε₁le, hthird⟩ :=
    exists_third_deriv_bound (m := m) (k := k) (x := x) (ε := ε) (C := C) (ν := ν) (Cv := Cv)
      hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode hsep hv hI
  set L : ℝ := (4:ℝ)/9 * κ + 1 with hL
  have hLpos : 0 < L := by rw [hL]; positivity
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      (4:ℝ)/9 * κ / 2 < deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
        * t ^ ((2:ℝ)/3) ∧
      deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t * t ^ ((2:ℝ)/3) < L := by
    have h := hSec.eventually (isOpen_Ioo.mem_nhds
      (show (4:ℝ)/9 * κ ∈ Ioo ((4:ℝ)/9 * κ / 2) L by
        rw [Set.mem_Ioo, hL]; constructor <;> linarith))
    filter_upwards [h] with t ht
    exact ⟨ht.1, ht.2⟩
  refine ⟨e * L ^ ((5:ℝ)/2), by positivity, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT hε₁pos] with t ht hεt
  have ht0 : 0 < t := hεt.1
  have ht23 : 0 < t ^ ((2:ℝ)/3) := Real.rpow_pos_of_pos ht0 _
  have hÏpos : 0 < deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t := by
    by_contra hle
    push Not at hle
    nlinarith [ht.1, ht23, mul_nonpos_of_nonpos_of_nonneg hle ht23.le]
  have hthird' : |deriv (deriv (deriv (fun s : ℝ => clusterInertia m k (x s)))) t|
      ≤ e * (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t) ^ ((5:ℝ)/2) := by
    have h := hthird t hεt
    rwa [show ((2 * 4 - 3) / (4 - 2) : ℝ) = (5:ℝ)/2 by norm_num] at h
  calc |t ^ ((5:ℝ)/3) * deriv (deriv (deriv (fun s : ℝ => clusterInertia m k (x s)))) t|
      = t ^ ((5:ℝ)/3)
          * |deriv (deriv (deriv (fun s : ℝ => clusterInertia m k (x s)))) t| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ ((5:ℝ)/3))]
    _ ≤ t ^ ((5:ℝ)/3)
          * (e * (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t) ^ ((5:ℝ)/2)) :=
        mul_le_mul_of_nonneg_left hthird' (by positivity)
    _ = e * (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
          * t ^ ((2:ℝ)/3)) ^ ((5:ℝ)/2) := by
        rw [show t ^ ((5:ℝ)/3) = (t ^ ((2:ℝ)/3)) ^ ((5:ℝ)/2) by
              rw [← Real.rpow_mul ht0.le]; norm_num,
          Real.mul_rpow hÏpos.le (Real.rpow_nonneg ht0.le _)]
        ring
    _ ≤ e * L ^ ((5:ℝ)/2) := by
        refine mul_le_mul_of_nonneg_left ?_ hepos.le
        exact Real.rpow_le_rpow (by positivity) ht.2.le (by norm_num)

/-- **The third derivative of `√(I_k)` along a motion.**  The derivative of `φ''` is
`I⃛/(2√I) - 3*İ*Ï/(4(√I)^3) + 3*İ^3/(8(√I)^5)` (where `İ`, `Ï`, `I⃛` denote the first three
derivatives of `I_k ∘ x`). -/
lemma hasDerivAt_deriv_deriv_clusterSqrtInertia_curve {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε t : ℝ} (ht : t ∈ Ioo (0:ℝ) ε)
    (hpos : ∀ τ ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x τ))
    (hx : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x τ) τ)
    (hd2 : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x τ) τ)
    (hd3 : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) τ) τ) :
    HasDerivAt (deriv (deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s)))))
      (deriv (deriv (deriv (fun s : ℝ => clusterInertia m k (x s)))) t
          / (2 * Real.sqrt (clusterInertia m k (x t)))
        - 3 * deriv (fun s : ℝ => clusterInertia m k (x s)) t
            * deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
          / (4 * (Real.sqrt (clusterInertia m k (x t))) ^ 3)
        + 3 * (deriv (fun s : ℝ => clusterInertia m k (x s)) t) ^ 3
          / (8 * (Real.sqrt (clusterInertia m k (x t))) ^ 5)) t := by
  set A : ℝ → ℝ := (fun τ : ℝ => deriv (fun u : ℝ => clusterInertia m k (x u)) τ) with hAdef
  set B : ℝ → ℝ := (fun τ : ℝ => deriv (deriv (fun u : ℝ => clusterInertia m k (x u))) τ)
    with hBdef
  set C : ℝ → ℝ :=
    (fun τ : ℝ => deriv (deriv (deriv (fun u : ℝ => clusterInertia m k (x u)))) τ) with hCdef
  set s : ℝ → ℝ := (fun τ : ℝ => Real.sqrt (clusterInertia m k (x τ))) with hsdef
  have hev : ∀ᶠ τ in 𝓝 t, HasDerivAt x (deriv x τ) τ := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
    exact hx τ hτ
  have hd2' : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (deriv (deriv x) τ) τ :=
    fun τ hτ => (hd2 τ hτ).congr_deriv (iteratedDeriv_two_eq_deriv_deriv x τ)
  have hs0 : s t ≠ 0 := by
    rw [hsdef]
    exact ne_of_gt (Real.sqrt_pos.mpr (hpos t ht))
  have hAt : HasDerivAt A (B t) t := by
    have h := hasDerivAt_deriv_clusterInertia_curve (m := m) (k := k) (x := x) hev (hd2' t ht)
    simpa only [hAdef, hBdef] using h
  have hBt : HasDerivAt B (C t) t := by
    have h := hasDerivAt_deriv_deriv_clusterInertia_curve (m := m) (k := k) (x := x)
      (ε := ε) ht hx hd2' hd3
    simpa only [hBdef, hCdef] using h
  have hst : HasDerivAt s (A t / (2 * s t)) t := by
    have h := hasDerivAt_clusterSqrtInertia_curve (m := m) (k := k) (x := x) (hpos t ht) hev
    refine h.congr_deriv ?_
    simp only [hAdef, hsdef]
  have hF : HasDerivAt (fun τ : ℝ => B τ / (2 * s τ) - (A τ) ^ 2 / (4 * (s τ) ^ 3))
      (C t / (2 * s t) - 3 * A t * B t / (4 * (s t) ^ 3)
        + 3 * (A t) ^ 3 / (8 * (s t) ^ 5)) t := by
    have h1 : HasDerivAt (fun τ : ℝ => B τ / (2 * s τ))
        ((C t * (2 * s t) - B t * (2 * (A t / (2 * s t)))) / (2 * s t) ^ 2) t :=
      hBt.div (hst.const_mul 2) (mul_ne_zero two_ne_zero hs0)
    have h2 : HasDerivAt (fun τ : ℝ => (A τ) ^ 2 / (4 * (s τ) ^ 3))
        (((2 * (A t) ^ 1 * B t) * (4 * (s t) ^ 3)
          - (A t) ^ 2 * (4 * (3 * (s t) ^ 2 * (A t / (2 * s t)))))
            / (4 * (s t) ^ 3) ^ 2) t :=
      (hAt.pow 2).div ((hst.pow 3).const_mul 4)
        (mul_ne_zero (by norm_num) (pow_ne_zero 3 hs0))
    refine (h1.sub h2).congr_deriv ?_
    field_simp
    ring
  have hD : deriv (deriv (fun u : ℝ => Real.sqrt (clusterInertia m k (x u)))) =ᶠ[𝓝 t]
      (fun τ : ℝ => B τ / (2 * s τ) - (A τ) ^ 2 / (4 * (s τ) ^ 3)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
    have h := hasDerivAt_deriv_clusterSqrtInertia_curve (m := m) (k := k) (x := x)
      (ε := ε) (t := τ) hτ hpos hx hd2
    have hv : deriv (deriv (fun u : ℝ => Real.sqrt (clusterInertia m k (x u)))) τ
        = B τ / (2 * s τ) - (A τ) ^ 2 / (4 * (s τ) ^ 3) := by
      exact h.deriv
    exact hv
  simpa only [hAdef, hBdef, hCdef, hsdef] using (hF.congr_of_eventuallyEq hD)

end Submission.NBody


