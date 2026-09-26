import Mathlib
import Submission.Work.Core.Torus
import Submission.Work.Core.torusMap_eq_iff
import Submission.Work.Extract.Defs

/-!
# The parametrised torus `ψ = Φ.Hinv 1 ∘ torusMap` of an ambient isotopy

Given an ambient isotopy `Φ` of `ℝ³`, the map

  `ψ := fun p : ℝ × ℝ => Φ.Hinv 1 (Work.Core.torusMap p.1 p.2)`

is a smooth `2π`-periodic parametrisation of an embedded torus which is injective
modulo `2π` and whose derivative is uniformly bounded below:

  `∃ c > 0, ∀ p u, c * ‖u‖ ≤ ‖fderiv ℝ ψ p u‖`.

The proof of the derivative bound has two ingredients.

* `psi_aux_torusFun_fderiv_lower`: for the standard torus parametrisation
  `torusFun p = torusMap p.1 p.2`, the derivative dominates the identity.  Indeed,
  writing `a = 2 + cos φ` the two partial derivatives
  `∂/∂θ = (-a sin θ, a cos θ, 0)` and `∂/∂φ = (-sin φ cos θ, -sin φ sin θ, cos φ)`
  are orthogonal with norms `a ≥ 1` and `1`, so for `u = (u₁, u₂)`
  `‖D torusFun p u‖² = u₁² a² + u₂² ≥ u₁² + u₂² ≥ max(u₁², u₂²) = ‖u‖²`.

* `psi_aux_psiFun_fderiv_lower`: the derivative of `Φ.Hinv 1` at `q` expands by
  at least `‖fderiv (Φ.H 1) (Φ.Hinv 1 q)‖⁻¹`, by the chain rule for the two inverse
  diffeomorphisms.  The function `q ↦ ‖fderiv (Φ.H 1) (Φ.Hinv 1 q)‖` is continuous
  and positive, and `q` ranges over the image of the compact fundamental domain
  `[0, 2π]²`; this gives a uniform constant on the fundamental domain, transported
  to all of `ℝ²` by the periodicity of `ψ`.

The remaining conclusions (periodicity in each variable, injectivity modulo `2π`,
continuity) are immediate from the definition, `Work.Core.torusMap_eq_iff`, and the
smoothness of `Φ.Hinv 1`.
-/

open LeanEval.KnotTheory.PardonDistortion

namespace Work.Extract

noncomputable section

/-! ### One-variable calculus helpers -/

private lemma psi_aux_line_hasDerivAt (p u : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => p + t • u) u 0 := by
  have h1 : HasDerivAt (fun t : ℝ => t • u) u 0 := by
    have h := (hasDerivAt_id (0:ℝ)).smul_const u
    simpa using h
  simpa using h1.const_add p

private lemma psi_aux_hasDerivAt_cos_shift (a b : ℝ) :
    HasDerivAt (fun t : ℝ => Real.cos (a + t * b)) (-Real.sin a * b) 0 := by
  have h : HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t * b) b 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).mul_const b
    simpa using h1.const_add a
  simpa using h.cos

private lemma psi_aux_hasDerivAt_sin_shift (a b : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin (a + t * b)) (Real.cos a * b) 0 := by
  have h : HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t * b) b 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).mul_const b
    simpa using h1.const_add a
  simpa using h.sin

/-- The `i`-th coordinate of a derivative is the derivative of the `i`-th coordinate. -/
private lemma psi_aux_hasDerivAt_apply (i : Fin 3) {f : ℝ → R3} {f' : R3} {t : ℝ}
    (hf : HasDerivAt f f' t) : HasDerivAt (fun s => f s i) (f' i) t := by
  let P : R3 →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i
  have h : HasDerivAt (P ∘ f) (P f') t :=
    (ContinuousLinearMap.hasFDerivAt P).comp_hasDerivAt t hf
  have h3 : P f' = f' i := rfl
  rw [h3] at h
  simpa [Function.comp_def, PiLp.proj_apply, P] using h

/-- Continuity of the standard torus parametrisation, in the instance shape used by the
target statement (`Continuous (fun p : ℝ × ℝ => torusMap p.1 p.2)`). -/
private theorem psi_aux_torusMap_continuous :
    Continuous (fun p : ℝ × ℝ => Work.Core.torusMap p.1 p.2) := by
  have h : Continuous (fun p : ℝ × ℝ => fun i : Fin 3 =>
      (if i.val = 0 then (2 + Real.cos p.2) * Real.cos p.1
       else if i.val = 1 then (2 + Real.cos p.2) * Real.sin p.1
       else Real.sin p.2 : ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp h

/-! ### The derivative of the standard torus parametrisation dominates the identity -/

private lemma psi_aux_torusFun_fderiv_lower (p u : ℝ × ℝ) :
    ‖u‖ ≤ ‖fderiv ℝ torusFun p u‖ := by
  have hderiv : HasDerivAt (fun t : ℝ => torusFun (p + t • u)) (fderiv ℝ torusFun p u) 0 := by
    have hd' : HasFDerivAt torusFun (fderiv ℝ torusFun p) (p + (0:ℝ) • u) := by
      simpa using (torusFun_differentiable p).hasFDerivAt
    have h := hd'.comp_hasDerivAt 0 (psi_aux_line_hasDerivAt p u)
    simpa [Function.comp_def] using h
  have hcoord0 : (fderiv ℝ torusFun p u) 0 =
      -(Real.sin p.2) * u.2 * Real.cos p.1 - (2 + Real.cos p.2) * Real.sin p.1 * u.1 := by
    have hfun : (fun t : ℝ => torusFun (p + t • u) 0) =
        fun t : ℝ => (2 + Real.cos (p.2 + t * u.2)) * Real.cos (p.1 + t * u.1) := by
      funext t
      rw [torusFun_apply, Work.Core.torusMap_apply_zero]
      simp
    have h1 := psi_aux_hasDerivAt_apply 0 hderiv
    rw [hfun] at h1
    have hbase := ((psi_aux_hasDerivAt_cos_shift p.2 u.2).const_add 2).mul
      (psi_aux_hasDerivAt_cos_shift p.1 u.1)
    have h2 := h1.unique hbase
    rw [h2]
    simp only [zero_mul, add_zero]
    ring
  have hcoord1 : (fderiv ℝ torusFun p u) 1 =
      -(Real.sin p.2) * u.2 * Real.sin p.1 + (2 + Real.cos p.2) * Real.cos p.1 * u.1 := by
    have hfun : (fun t : ℝ => torusFun (p + t • u) 1) =
        fun t : ℝ => (2 + Real.cos (p.2 + t * u.2)) * Real.sin (p.1 + t * u.1) := by
      funext t
      rw [torusFun_apply, Work.Core.torusMap_apply_one]
      simp
    have h1 := psi_aux_hasDerivAt_apply 1 hderiv
    rw [hfun] at h1
    have hbase := ((psi_aux_hasDerivAt_cos_shift p.2 u.2).const_add 2).mul
      (psi_aux_hasDerivAt_sin_shift p.1 u.1)
    have h2 := h1.unique hbase
    rw [h2]
    simp only [zero_mul, add_zero]
    ring
  have hcoord2 : (fderiv ℝ torusFun p u) 2 = Real.cos p.2 * u.2 := by
    have hfun : (fun t : ℝ => torusFun (p + t • u) 2) =
        fun t : ℝ => Real.sin (p.2 + t * u.2) := by
      funext t
      rw [torusFun_apply, Work.Core.torusMap_apply_two]
      simp
    have h1 := psi_aux_hasDerivAt_apply 2 hderiv
    rw [hfun] at h1
    exact h1.unique (psi_aux_hasDerivAt_sin_shift p.2 u.2)
  have hnorm : ‖fderiv ℝ torusFun p u‖ ^ 2 =
      (-(Real.sin p.2) * u.2 * Real.cos p.1 - (2 + Real.cos p.2) * Real.sin p.1 * u.1) ^ 2
      + (-(Real.sin p.2) * u.2 * Real.sin p.1 + (2 + Real.cos p.2) * Real.cos p.1 * u.1) ^ 2
      + (Real.cos p.2 * u.2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, hcoord0, hcoord1, hcoord2]
  have ha : (1:ℝ) ≤ (2 + Real.cos p.2) ^ 2 := by
    nlinarith [Real.neg_one_le_cos p.2]
  have hw : ‖fderiv ℝ torusFun p u‖ ^ 2 =
      u.1 ^ 2 * (2 + Real.cos p.2) ^ 2 + u.2 ^ 2 := by
    rw [hnorm]
    have h1 := Real.sin_sq_add_cos_sq p.1
    have h2 := Real.sin_sq_add_cos_sq p.2
    linear_combination
      (Real.sin p.2 ^ 2 * u.2 ^ 2 + (2 + Real.cos p.2) ^ 2 * u.1 ^ 2) * h1
      + (u.2 ^ 2) * h2
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  apply max_le
  · have hsq : u.1 ^ 2 ≤ ‖fderiv ℝ torusFun p u‖ ^ 2 := by
      rw [hw]
      nlinarith [mul_le_mul_of_nonneg_left ha (sq_nonneg u.1), sq_nonneg u.2]
    have h := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (norm_nonneg _)] at h
  · have hsq : u.2 ^ 2 ≤ ‖fderiv ℝ torusFun p u‖ ^ 2 := by
      rw [hw]
      nlinarith [sq_nonneg (u.1 * (2 + Real.cos p.2))]
    have h := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (norm_nonneg _)] at h

/-! ### Uniform lower bound for the derivative of `ψ = Φ.Hinv 1 ∘ torusFun` -/

/-- The period vector of the parameter plane attached to an integer pair. -/
private def psi_aux_periodVec (v : ℤ × ℤ) : ℝ × ℝ :=
  ((v.1 : ℝ) * (2 * Real.pi), (v.2 : ℝ) * (2 * Real.pi))

private lemma psi_aux_torusFun_add_periodVec (p : ℝ × ℝ) (v : ℤ × ℤ) :
    torusFun (p + psi_aux_periodVec v) = torusFun p := by
  obtain ⟨k, l⟩ := v
  have h1 : Function.Periodic
      (fun x : ℝ => torusFun (x, p.2 + (l : ℝ) * (2 * Real.pi))) (2 * Real.pi) :=
    fun x => torusFun_periodic_left x (p.2 + (l : ℝ) * (2 * Real.pi))
  have h2 : Function.Periodic (fun y : ℝ => torusFun (p.1, y)) (2 * Real.pi) :=
    fun y => torusFun_periodic_right p.1 y
  have hk1 : torusFun (p.1 + (k : ℝ) * (2 * Real.pi), p.2 + (l : ℝ) * (2 * Real.pi)) =
      torusFun (p.1, p.2 + (l : ℝ) * (2 * Real.pi)) := by
    simpa [zsmul_eq_mul] using h1.int_mul k p.1
  have hk2 : torusFun (p.1, p.2 + (l : ℝ) * (2 * Real.pi)) = torusFun (p.1, p.2) := by
    simpa [zsmul_eq_mul] using h2.int_mul l p.2
  exact hk1.trans hk2

private lemma psi_aux_psiFun_add_periodVec (Φ : AmbientIsotopy) (p : ℝ × ℝ) (v : ℤ × ℤ) :
    psiFun Φ (p + psi_aux_periodVec v) = psiFun Φ p := by
  simp only [psiFun_apply, psi_aux_torusFun_add_periodVec]

private lemma psi_aux_exists_int_sub_mem_Icc (t : ℝ) :
    ∃ k : ℤ, t - (k : ℝ) * (2 * Real.pi) ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
  refine ⟨⌊t / (2 * Real.pi)⌋, ?_⟩
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h : t - (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)
      = Int.fract (t / (2 * Real.pi)) * (2 * Real.pi) := by
    rw [Int.fract]; field_simp
  rw [Set.mem_Icc, h]
  exact ⟨mul_nonneg (Int.fract_nonneg _) hpos.le, by
    have hm := mul_lt_mul_of_pos_right (Int.fract_lt_one (t / (2 * Real.pi))) hpos
    linarith⟩

private lemma psi_aux_exists_periodVec_add_mem_box (p : ℝ × ℝ) :
    ∃ v : ℤ × ℤ, p + psi_aux_periodVec v ∈
      Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi) := by
  obtain ⟨k, hk⟩ := psi_aux_exists_int_sub_mem_Icc p.1
  obtain ⟨l, hl⟩ := psi_aux_exists_int_sub_mem_Icc p.2
  refine ⟨(-k, -l), ?_⟩
  have h₁ : p.1 + (((-k : ℤ)) : ℝ) * (2 * Real.pi) = p.1 - (k : ℝ) * (2 * Real.pi) := by
    push_cast; ring
  have h₂ : p.2 + (((-l : ℤ)) : ℝ) * (2 * Real.pi) = p.2 - (l : ℝ) * (2 * Real.pi) := by
    push_cast; ring
  rw [Set.mem_prod]
  simp only [psi_aux_periodVec, Prod.fst_add, Prod.snd_add]
  rw [h₁, h₂]
  exact ⟨hk, hl⟩

private theorem psi_aux_psiFun_fderiv_lower (Φ : AmbientIsotopy)
    (hT : ∀ p u : ℝ × ℝ, ‖u‖ ≤ ‖fderiv ℝ torusFun p u‖) :
    ∃ c : ℝ, 0 < c ∧ ∀ p u : ℝ × ℝ,
      c * ‖u‖ ≤ ‖fderiv ℝ (psiFun Φ) p u‖ := by
  set G : ℝ × ℝ → ℝ := fun p => ‖fderiv ℝ (forwMap Φ) (invMap Φ (torusFun p))‖ with hG
  have hGcont : Continuous G := by
    rw [hG]
    have h1 : Continuous (fderiv ℝ (forwMap Φ)) :=
      (forwMap_contDiff Φ).continuous_fderiv (by simp)
    have h2 : Continuous (fun p : ℝ × ℝ => invMap Φ (torusFun p)) :=
      (invMap_contDiff Φ).continuous.comp torusFun_contDiff.continuous
    exact (h1.comp h2).norm
  have hpoint : ∀ p u : ℝ × ℝ, ‖u‖ ≤ G p * ‖fderiv ℝ (psiFun Φ) p u‖ := by
    intro p u
    rw [hG]
    have hv := norm_le_opNorm_mul_norm_fderiv Φ (torusFun p) (fderiv ℝ torusFun p u)
    have hf : fderiv ℝ (psiFun Φ) p u
        = (fderiv ℝ (invMap Φ) (torusFun p)) (fderiv ℝ torusFun p u) := by
      rw [fderiv_psiFun Φ p]
      rfl
    rw [hf]
    linarith [hv, hT p u]
  let D : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)
  have hDcompact : IsCompact D := isCompact_Icc.prod isCompact_Icc
  have hDne : D.Nonempty :=
    ⟨(0, 0), ⟨⟨le_refl 0, Real.two_pi_pos.le⟩, ⟨le_refl 0, Real.two_pi_pos.le⟩⟩⟩
  obtain ⟨p₀, hp₀D, hp₀max⟩ := hDcompact.exists_isMaxOn hDne hGcont.continuousOn
  have hGpos : 0 < G p₀ := by
    rw [hG]
    exact norm_pos_iff.mpr (fderiv_forwMap_ne_zero Φ (torusFun p₀))
  refine ⟨1 / G p₀, div_pos one_pos hGpos, ?_⟩
  intro p u
  obtain ⟨v, hv⟩ := psi_aux_exists_periodVec_add_mem_box p
  have hfder : fderiv ℝ (psiFun Φ) p = fderiv ℝ (psiFun Φ) (p + psi_aux_periodVec v) := by
    have hfun : psiFun Φ ∘ (fun x : ℝ × ℝ => x + psi_aux_periodVec v) = psiFun Φ := by
      funext x
      exact psi_aux_psiFun_add_periodVec Φ x v
    have hSdiff : DifferentiableAt ℝ (fun x : ℝ × ℝ => x + psi_aux_periodVec v) p := by
      fun_prop
    have hcomp := fderiv_comp (𝕜 := ℝ) p (f := fun x : ℝ × ℝ => x + psi_aux_periodVec v)
      (g := psiFun Φ) ((psiFun_differentiable Φ) (p + psi_aux_periodVec v)) hSdiff
    rw [hfun] at hcomp
    have hS : fderiv ℝ (fun x : ℝ × ℝ => x + psi_aux_periodVec v) p = 1 := by
      have h : HasFDerivAt (fun x : ℝ × ℝ => x + psi_aux_periodVec v)
          (1 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
        simpa [ContinuousLinearMap.one_def] using
          (hasFDerivAt_id (𝕜 := ℝ) p).add_const (psi_aux_periodVec v)
      exact h.fderiv
    rw [hS, ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id] at hcomp
    exact hcomp
  have hbound := hpoint (p + psi_aux_periodVec v) u
  have hGle : G (p + psi_aux_periodVec v) ≤ G p₀ := hp₀max hv
  calc (1 / G p₀) * ‖u‖
      ≤ (1 / G p₀) * (G (p + psi_aux_periodVec v) *
          ‖fderiv ℝ (psiFun Φ) (p + psi_aux_periodVec v) u‖) := by
        apply mul_le_mul_of_nonneg_left hbound
        positivity
    _ = (G (p + psi_aux_periodVec v) / G p₀) *
          ‖fderiv ℝ (psiFun Φ) (p + psi_aux_periodVec v) u‖ := by ring
    _ ≤ 1 * ‖fderiv ℝ (psiFun Φ) (p + psi_aux_periodVec v) u‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [div_le_one hGpos]
        exact hGle
    _ = ‖fderiv ℝ (psiFun Φ) (p + psi_aux_periodVec v) u‖ := by rw [one_mul]
    _ = ‖fderiv ℝ (psiFun Φ) p u‖ := by rw [hfder]

/-! ### The structure of `ψ` -/

theorem psi_structure (Φ : LeanEval.KnotTheory.PardonDistortion.AmbientIsotopy) :
    ∃ c : ℝ, 0 < c ∧
      (∀ x y : ℝ, (fun x y => Φ.Hinv 1 (Work.Core.torusMap x y)) (x + 2 * Real.pi) y
          = (fun x y => Φ.Hinv 1 (Work.Core.torusMap x y)) x y) ∧
      (∀ x y : ℝ, (fun x y => Φ.Hinv 1 (Work.Core.torusMap x y)) x (y + 2 * Real.pi)
          = (fun x y => Φ.Hinv 1 (Work.Core.torusMap x y)) x y) ∧
      (∀ x y x' y' : ℝ, (fun x y => Φ.Hinv 1 (Work.Core.torusMap x y)) x y
          = (fun x y => Φ.Hinv 1 (Work.Core.torusMap x y)) x' y' ↔
        (∃ k : ℤ, x = x' + k * (2 * Real.pi)) ∧ (∃ k : ℤ, y = y' + k * (2 * Real.pi))) ∧
      Continuous (fun p : ℝ × ℝ => Φ.Hinv 1 (Work.Core.torusMap p.1 p.2)) ∧
      (∀ p : ℝ × ℝ, ∀ u : ℝ × ℝ,
        c * ‖u‖ ≤ ‖fderiv ℝ (fun p : ℝ × ℝ => Φ.Hinv 1 (Work.Core.torusMap p.1 p.2)) p u‖) := by
  obtain ⟨c, hcpos, hc⟩ :=
    psi_aux_psiFun_fderiv_lower Φ psi_aux_torusFun_fderiv_lower
  have hinj : Function.Injective (fun v : R3 => Φ.Hinv 1 v) := fun a b hab => by
    have h := congrArg (fun v : R3 => Φ.H 1 v) hab
    rwa [Φ.inv_right 1 a, Φ.inv_right 1 b] at h
  refine ⟨c, hcpos, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    show Φ.Hinv 1 (Work.Core.torusMap (x + 2 * Real.pi) y) = Φ.Hinv 1 (Work.Core.torusMap x y)
    simpa only [psiFun_apply, torusFun_apply] using psiFun_periodic_left Φ x y
  · intro x y
    show Φ.Hinv 1 (Work.Core.torusMap x (y + 2 * Real.pi)) = Φ.Hinv 1 (Work.Core.torusMap x y)
    simpa only [psiFun_apply, torusFun_apply] using psiFun_periodic_right Φ x y
  · intro x y x' y'
    show Φ.Hinv 1 (Work.Core.torusMap x y) = Φ.Hinv 1 (Work.Core.torusMap x' y') ↔
      (∃ k : ℤ, x = x' + k * (2 * Real.pi)) ∧ (∃ k : ℤ, y = y' + k * (2 * Real.pi))
    rw [show (Φ.Hinv 1 (Work.Core.torusMap x y) = Φ.Hinv 1 (Work.Core.torusMap x' y') ↔
        Work.Core.torusMap x y = Work.Core.torusMap x' y') from
        ⟨fun h => hinj h, fun h => by rw [h]⟩]
    exact Work.Core.torusMap_eq_iff x y x' y'
  · show Continuous (fun p : ℝ × ℝ => Φ.Hinv 1 (Work.Core.torusMap p.1 p.2))
    have h1 : Continuous (fun v : R3 => Φ.Hinv 1 v) := (invMap_contDiff Φ).continuous
    exact h1.comp psi_aux_torusMap_continuous
  · intro p u
    show c * ‖u‖ ≤
      ‖fderiv ℝ (fun p : ℝ × ℝ => Φ.Hinv 1 (Work.Core.torusMap p.1 p.2)) p u‖
    exact hc p u

end

end Work.Extract
